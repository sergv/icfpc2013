----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Copyright   :  (c) Sergey Vinokurov 2013
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Main where

import Control.Applicative (pure, (<$>), (<*>), (<|>))
import Control.Monad (liftM, mzero, mplus, mapM_)

import Data.Aeson ((.:), (.:?), (.=), object, encode, decode, decode',
                   FromJSON(..), Value(..), ToJSON(..))
import Data.Attoparsec.Char8
import Data.Bits
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.ByteString.Char8 as SBS
import Data.Functor (fmap)
import Data.HashMap.Strict as HM
import Data.IORef
import Data.List (sortBy)
import Data.Ord (compare)
import Data.Typeable
import Data.Text as T
import Data.Vector as V ((!))
import Data.Word

import Network.Curl hiding (curlPost)

import Numeric (showHex, readHex)
import Text.Printf

import Debug.Trace (trace)

eitherDecode, eitherDecode' :: (Show a, FromJSON a) => BS.ByteString -> Either String a
eitherDecode input = maybe (Left $ "decoding failed for " ++ BS.unpack input) Right $ decode input
eitherDecode' input = maybe (Left $ "decoding failed for " ++ BS.unpack input) Right $ decode' input

----- Utilities

url = "icfpc2013.cloudapp.net"
auth = "0136KzBjC6HM0KdaVr1KOsK1nCeYPXRLFD9Gp4pm"
suffix = "vpsH1H"

curlPost :: URLString -> String -> IO (Int, String)
curlPost path content = do
    handle <- initialize
    responseStore <- (newIORef []) :: IO (IORef [String])
    let full_url = ("http://" ++ url ++ "/" ++ path ++ "?auth=" ++ auth ++ suffix)
        body = HttpPost "" Nothing (ContentString content) [] Nothing
        opts = [ CurlURL full_url
               , CurlVerbose False
               , CurlHeader False
               , CurlNoProgress True
               , CurlPost True
               -- , CurlHttpPost [body]
               , CurlPostFields [content]
               , CurlWriteFunction $ gatherOutput responseStore
               , CurlHeaderFunction ignoreOutput
               , CurlFailOnError True
               ]
    mapM_ (setopt handle) opts
    perform handle
    code <- {-fmap toCode $-} getResponseCode handle
    output <- readIORef responseStore
    return (code, Prelude.foldr (++) [] output)

request :: (Show a, FromJSON a) => URLString -> String -> (Int -> String) -> IO (Either String a)
request path content err_func = do
    (code, output) <- Main.curlPost path content
    if code == 200
    then return $ eitherDecode' $ BS.pack output
    else return $ Left $ err_func code

    -- setopt handle CurlURL ("http://" ++ url ++ "/" ++ path ++ "?auth=" ++ auth ++ suffix)
    -- setopt handle CurlVerbose True
    -- setopt handle CurlHeader True
    -- setopt handle CurlNoProgress True
    -- setopt handle CurlPost True
    -- setopt handle CurlHttpPost (HttpPost "" Nothing (ContentString content) [] Nothing)
    -- perform handle

read_hex :: String -> Word64
read_hex ('0': 'x': rest) = read_hex rest
read_hex num              = fst $ Prelude.head $ readHex num

args_to_hex :: [Word64] -> [String]
args_to_hex args = if Prelude.length args > 256
                   then error $ printf "requested too much arguments to evaluate: <= 256 allowed but %d given" (Prelude.length args)
                   else Prelude.map (\arg -> "0x" ++ showHex arg "") args


----- Program

type Id = String
data Program = Lambda Id Expression
             deriving (Show, Eq, Read)
data Expression = Literal Word64
                | Id Id
                | If0 Expression Expression Expression
                | Fold Expression Expression Id Id Expression
                | Op1 Op1 Expression
                | Op2 Op2 Expression Expression
                deriving (Show, Eq, Read)
data Op1 = Not | Shl | Shr | Shr4 | Shr16
         deriving (Show, Eq, Read)
data Op2 = And | Or | Xor | Plus
         deriving (Show, Eq, Read)

---- sexp encoding

class ProgramSexpEncode a where
    encodeSexp :: a -> String

instance ProgramSexpEncode Id where
    encodeSexp x = x

instance ProgramSexpEncode Op1 where
    encodeSexp Not   = "not"
    encodeSexp Shl   = "shl1"
    encodeSexp Shr   = "shr1"
    encodeSexp Shr4  = "shr4"
    encodeSexp Shr16 = "shr16"


instance ProgramSexpEncode Op2 where
    encodeSexp And  = "and"
    encodeSexp Or   = "or"
    encodeSexp Xor  = "xor"
    encodeSexp Plus = "plus"

-- optional space to aid debugging
optS = " "

instance ProgramSexpEncode Program where
    encodeSexp (Lambda x e) =
        "(lambda" ++ optS ++ "(" ++ encodeSexp x ++ ")" ++ optS ++ encodeSexp e ++ ")"

instance ProgramSexpEncode Expression where
    encodeSexp (Literal w) = show w
    encodeSexp (Id id)     = encodeSexp id
    encodeSexp (If0 c t e) =
        "(if0 " ++ encodeSexp c ++ " " ++ encodeSexp t ++ " " ++ encodeSexp e ++ ")"
    encodeSexp (Fold e1 e2 id1 id2 e3) =
        "(fold " ++ encodeSexp e1 ++ " " ++ encodeSexp e2 ++ optS ++
            "(lambda" ++ optS ++ "(" ++ encodeSexp id1 ++ " " ++
                                        encodeSexp id2 ++ ")" ++ optS ++
                encodeSexp e3 ++
            ")" ++
        ")"
    encodeSexp (Op1 op arg) =
        "(" ++ encodeSexp op ++ " " ++ encodeSexp arg ++ ")"
    encodeSexp (Op2 op arg1 arg2) =
        "(" ++ encodeSexp op ++ " " ++ encodeSexp arg1 ++ " " ++ encodeSexp arg2 ++ ")"

---- sexp decoding

decodeSexp' :: String -> Either String Program
decodeSexp' = decodeSexp . SBS.pack

decodeSexpUnsafe :: SBS.ByteString -> Program
decodeSexpUnsafe input =
    case decodeSexp input of
        Right prog -> prog
        Left err -> error $ "decodeSexpUnsafe: error while decoding program: " ++ err


decodeSexp :: SBS.ByteString -> Either String Program
decodeSexp input = parseOnly programParser input
    where
        whitespace :: Parser ()
        whitespace = skipWhile isWhitespace
            where
                isWhitespace :: Char -> Bool
                isWhitespace c = c == ' ' || c == '\t' || c == '\n' || c == '\r'

        optws :: Parser a -> Parser a
        optws p = whitespace >> p

        openParen, closeParen :: Parser ()
        openParen  = optws $ char '(' >> return ()
        closeParen = optws $ char ')' >> return ()

        programParser :: Parser Program
        programParser = do
            openParen
            optws $ string "lambda"
            openParen
            id <- optws identifier
            closeParen
            expr <- expression
            closeParen
            optws endOfInput
            return $ Lambda id expr

        expression :: Parser Expression
        expression =
            optws (
                (char '0' >> return (Literal 0)) <|>
                (char '1' >> return (Literal 1)) <|>
                (identifier >>= return . Id) <|>
                (openParen >> optws (ifExpr <|> foldExpr <|> op1expr <|> op2expr)))
            where
                ifExpr = do
                    string "if0"
                    c <- expression
                    t <- expression
                    e <- expression
                    closeParen
                    return $ If0 c t e
                foldExpr = do
                    string "fold"
                    e1 <- expression
                    e2 <- expression
                    openParen
                    optws $ string "lambda"
                    openParen
                    id1 <- optws identifier
                    id2 <- optws identifier
                    closeParen
                    e3 <- expression
                    closeParen
                    closeParen
                    return $ Fold e1 e2 id1 id2 e3
                op1expr = do
                    op <- optws op1Parser
                    arg <- expression
                    closeParen
                    return $ Op1 op arg
                op2expr = do
                    op <- optws op2Parser
                    arg1 <- expression
                    arg2 <- expression
                    closeParen
                    return $ Op2 op arg1 arg2

        identifier :: Parser Id
        identifier = do
            first <- satisfy lowercase
            rest <- Data.Attoparsec.Char8.takeWhile id_part
            return (first : SBS.unpack rest)
            where
                lowercase :: Char -> Bool
                lowercase c = c >= 'a' && c <= 'z'

                id_part :: Char -> Bool
                id_part c = lowercase c || c == '_' || c >= '0' && c <= '9'

        op1Parser :: Parser Op1
        op1Parser =
            (string "shr16" >> return Shr16) <|>
            (string "not" >> return Not)     <|>
            (string "shl1" >> return Shl)    <|>
            (string "shr1" >> return Shr)    <|>
            (string "shr4" >> return Shr4)
        op2Parser :: Parser Op2
        op2Parser =
            (string "and" >> return And) <|>
            (string "or" >> return Or)   <|>
            (string "xor" >> return Xor) <|>
            (string "plus" >> return Plus)

----- Problem

---- hints, problem datatype

data HintOp = HintOp1 Op1
            | HintOp2 Op2
            | HintIf0
            | HintTFold
            | HintFold
            deriving (Show, Eq, Read)

data Problem = Problem
             { problemId :: String
             , problemSize :: Int
             , problemOperators :: [HintOp]
             , problemSolved :: Maybe Bool
             , problemTimeLeft :: Maybe Float
             }
             deriving (Show, Eq, Read)

problem_store = "/home/sergey/projects/icfpc/2013_Aug/haskell/problems.store"

load_problems :: IO [Problem]
load_problems = readFile problem_store >>= return . read

type MayFailStr = Either String String

instance FromJSON Op1 where
    parseJSON (String s) =
        case s of
            "not"   -> pure Not
            "shl1"  -> pure Shl
            "shr1"  -> pure Shr
            "shr4"  -> pure Shr4
            "shr16" -> pure Shr16
            _       -> mzero
    parseJSON _          = mzero

instance FromJSON Op2 where
    parseJSON (String s) =
        case s of
            "and"  -> pure And
            "or"   -> pure Or
            "xor"  -> pure Xor
            "plus" -> pure Plus
            _      -> mzero
    parseJSON _          = mzero


instance FromJSON HintOp where
    parseJSON str@(String s) =
        case s of
            "if0"   -> pure HintIf0
            "tfold" -> pure HintTFold
            "fold"  -> pure HintFold
            _       -> mplus (fmap HintOp1 $ (parseJSON str)) (fmap HintOp2 $ (parseJSON str))
    parseJSON _          = mzero

instance FromJSON Problem where
    parseJSON (Object v) =
        Problem <$>
        (v .: "id") <*>
        (v .: "size") <*>
        (v .: "operators") <*>
        (v .:? "solved") <*>
        (v .:? "timeLeft")

---- Get problems request

get_problems :: IO (Either String [Problem])
get_problems = request "myproblems" "" analyze_error
    where
        analyze_error 403 =
            "get_problems failed: server informs: 403 authorization required"
        analyze_error 429 =
            "get_problems failed: server informs: 429 try again later"
        analyze_error x =
            (printf "get_problems failed: server informs: %d other error" x)


----- Evaluation

---- evaluate :: Program -> Word64 -> Word64

evaluate :: Program -> Word64 -> Word64
evaluate (Lambda var expr) input = eval expr (HM.singleton var input)

eval :: Expression -> HM.HashMap Id Word64 -> Word64
eval (Literal x) env               = x
eval (Id var)    env               = env HM.! var
eval (If0 c t e) env               = if 0 == eval c env then eval t env else eval e env
eval (Fold e1 e2 byte_var accum_var body_expr) env =
    let main_num   = eval e1 env
        init_acc   = eval e2 env
        -- byte n     = shiftR ((shiftL 0x00000000000000FF (n * 8)) .&. main_num) (n * 8)

        upd_env byte acc old_env =
            HM.insert byte_var byte $ HM.insert accum_var acc $ old_env
        byte n =
            shiftR main_num (n * 8) .&. 0x00000000000000FF

        iter 8 acc env = acc
        iter n acc old_env =
            let b   = byte n
                env = upd_env b acc old_env
                new_acc = eval body_expr env
            in iter (n + 1) new_acc env
    in  iter 0 init_acc env

eval (Op1 Not arg) env             = complement $ eval arg env
eval (Op1 Shl arg) env             = shiftL (eval arg env) 1
eval (Op1 Shr arg) env             = shiftR (eval arg env) 1
eval (Op1 Shr4 arg) env            = shiftR (eval arg env) 4
eval (Op1 Shr16 arg) env           = shiftR (eval arg env) 16

eval (Op2 And arg1 arg2) env       = (eval arg1 env) .&. (eval arg2 env)
eval (Op2 Or arg1 arg2) env        = (eval arg1 env) .|. (eval arg2 env)
eval (Op2 Xor arg1 arg2) env       = (eval arg1 env) `xor` (eval arg2 env)
eval (Op2 Plus arg1 arg2) env      = (eval arg1 env) + (eval arg2 env)


---- eval request

data EvalRequest = EvalId (Maybe Id) [Word64]
                 | EvalProgram Program [Word64]
                 deriving (Eq, Show)

instance ToJSON EvalRequest where
    toJSON (EvalId id args) =
        object ["id" .= id, "arguments" .= args_to_hex args]
    toJSON (EvalProgram program args) =
        object ["program" .= encodeSexp program, "arguments" .= args_to_hex args]

-- instance FromJSON EvalRequest where
--     parseJSON (Object v) =
--         EvalRequest <$> (v .:? "id") <$> (v .:? "program") <$> (v .: "arguments")


data EvalResponse = EvalError String -- error message
                  | EvalOk [Word64]
                  deriving (Eq, Show)

instance FromJSON EvalResponse where
    parseJSON (Object v) =
        case HM.lookup "status" v of
            Just "ok"    -> EvalOk <$> liftM (Prelude.map read_hex) (v .: "outputs")
            Just "error" -> EvalError <$> (v .: "message")
            _            -> error $ "invalid status of json eval response" ++ (show v)

eval_request :: EvalRequest -> IO (Either String EvalResponse)
eval_request req = request "eval" (BS.unpack $ encode req) analyze_error
    where
        analyze_error 400 =
            "eval_request failed: server informs: 400 bad request, malformed input"
        analyze_error 401 =
            "eval_request failed: server informs: 401 problem was not requested by the current user"
        analyze_error 404 =
            "eval_request failed: server informs: 404 no such challenge"
        analyze_error 410 =
            "eval_request failed: server informs: 410 too late: problem requested more than 5 minutes ago"
        analyze_error 412 =
            "eval_request failed: server informs: 412 problem already solved"
        analyze_error 413 =
            "eval_request failed: server informs: 413 request too big"
        analyze_error x =
            (printf "eval_request failed: server informs: %d other error" x)

----- Guesses

data GuessRequest = Guess String Program
                  deriving (Eq, Show)

instance ToJSON GuessRequest where
    toJSON (Guess id program) =
        object ["id" .= id, "program" .= encodeSexp program]

-- instance FromJSON EvalRequest where
--     parseJSON (Object v) =
--         EvalRequest <$> (v .:? "id") <$> (v .:? "program") <$> (v .: "arguments")


data GuessResponse = GuessWin
                   {- Input ValidResult InvalidResult (that our program got :) -}
                   | GuessMismatch String String String
                   | GuessError String -- error message
                   deriving (Eq, Show)

instance FromJSON GuessResponse where
    parseJSON (Object v) =
        case HM.lookup "status" v of
            Just "win"      -> pure GuessWin
            Just "mismatch" ->
                case HM.lookup "values" v of
                    Just (Array arr) ->
                        let v0 = arr V.! 0
                            v1 = arr V.! 1
                            v2 = arr V.! 2
                        in case (v0, v1, v2) of
                            (String input, String correct, String incorrect) ->
                                pure $ GuessMismatch (T.unpack input) (T.unpack correct) (T.unpack incorrect)
                            invalid                                          ->
                                error $ "invalid types of values field of GuessResponse, three strings expected: " ++ show invalid
                    invalid          ->
                        error $ "invalid values field of GuessResponse: " ++ show invalid
            Just "error"    -> GuessError <$> (v .: "message")
            _               -> error $ "invalid status of json eval response" ++ (show v)

guess_request :: GuessRequest -> IO (Either String GuessResponse)
guess_request req = request "guess" (BS.unpack $ encode req) analyze_error
    where
        analyze_error 400 =
            "guess_request failed: server informs: 400 bad request, malformed input"
        analyze_error 401 =
            "guess_request failed: server informs: 401 problem was not requested by the current user"
        analyze_error 404 =
            "guess_request failed: server informs: 404 no such challenge"
        analyze_error 410 =
            "guess_request failed: server informs: 410 too late: problem requested more than 5 minutes ago"
        analyze_error 412 =
            "guess_request failed: server informs: 412 problem already solved"
        analyze_error 413 =
            "guess_request failed: server informs: 413 request too big"
        analyze_error x =
            (printf "guess_request failed: server informs: %d other error" x)

---- Training

data TrainingOperator = RequestNoOperator
                      | RequestFoldOperator
                      | RequestTFoldOperator
                      deriving (Eq, Show)

data TrainingRequest = TrainingRequest Int TrainingOperator
                     deriving (Eq, Show)

instance ToJSON TrainingRequest where
    toJSON (TrainingRequest size operators) =
        object ["size" .= size, "operators" .= op]
        where
            op :: [String]
            op = case operators of
                RequestNoOperator -> []
                RequestFoldOperator -> ["fold"]
                RequestTFoldOperator -> ["tfold"]

-- instance FromJSON EvalRequest where
--     parseJSON (Object v) =
--         EvalRequest <$> (v .:? "id") <$> (v .:? "program") <$> (v .: "arguments")


           -- challenge id size operatros
data TrainingProblem = TrainingProblem
                     { trainingChallenge :: Program
                     , trainingId :: String
                     , trainingSize :: Int
                     , trainingOperators :: [HintOp]
                     }
                     deriving (Eq, Show)

instance FromJSON TrainingProblem where
    parseJSON (Object v) =
        TrainingProblem <$>
        liftM decodeSexpUnsafe (v .: "challenge") <*>
        (v .: "id") <*>
        (v .: "size") <*>
        (v .: "operators")

training_request :: TrainingRequest -> IO (Either String TrainingProblem)
training_request req = do
    let r = (BS.unpack $ encode req)
    printf "r = %s\n" r
    request "train" r analyze_error
    where
        analyze_error 400 =
            "guess_request failed: server informs: 400 bad request, malformed input"
        analyze_error 403 =
            "guess_request failed: server informs: 403 authorization required"
        analyze_error 429 =
            "guess_request failed: server informs: 429 try again later"
        analyze_error x =
            (printf "guess_request failed: server informs: %d other error" x)


main :: IO ()
main = do
     training_request (TrainingRequest 3 RequestNoOperator) >>= print

