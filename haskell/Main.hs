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
{-# LANGUAGE BangPatterns #-}

module Main where

import Control.Applicative (pure, (<$>), (<*>), (<|>))
import Control.Concurrent
import Control.Monad (liftM, mzero, mplus, mapM_)

import Data.Aeson ((.:), (.:?), (.=), object, encode, decode, decode',
                   FromJSON(..), Value(..), ToJSON(..))
import Data.Attoparsec.Char8
import Data.Bits
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.ByteString.Char8 as SBS
import Data.Functor (fmap)
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.IORef
import Data.List (sortBy)
import Data.Ord (compare)
import Data.Time
import Data.Typeable
import qualified Data.Text as T
import qualified Data.Vector as V ((!))
import Data.Word

import Network.Curl hiding (curlPost)

import Numeric (showHex, readHex)
import System.Random
import Text.Printf
import System.IO.Unsafe (unsafePerformIO)

import Debug.Trace (trace)

eitherDecode, eitherDecode' :: (Show a, FromJSON a) => BS.ByteString -> Either String a
eitherDecode input = maybe (Left $ "decoding failed for " ++ BS.unpack input) Right $ decode input
{-# INLINE eitherDecode #-}
eitherDecode' input = maybe (Left $ "decoding failed for " ++ BS.unpack input) Right $ decode' input
{-# INLINE eitherDecode' #-}

----- Utilities

url, auth, suffix :: String
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
               -- , CurlWriteFunction $ easyWriter (\s -> do
               --     printf "curl: got output chunk %s\n" s
               --     modifyIORef responseStore (++ [s]))
               , CurlHeaderFunction ignoreOutput
               , CurlFailOnError True
               ]
    mapM_ (setopt handle) opts
    perform handle
    code <- {-fmap toCode $-} getResponseCode handle
    output <- readIORef responseStore
    return (code, Prelude.foldr (++) [] $ Prelude.reverse output)

requestDelay :: Int
requestDelay = 4
{-# INLINE requestDelay #-}

prevRequestTime :: IORef UTCTime
prevRequestTime = unsafePerformIO (getCurrentTime >>= newIORef)
{-# NOINLINE prevRequestTime #-}

request :: (Show a, FromJSON a) => URLString -> String -> (Int -> String) -> IO (Either String a)
request path content err_func = do
    prev_time <- readIORef prevRequestTime
    time <- getCurrentTime
    let time_diff = (floor $ diffUTCTime time prev_time) :: Int
    if (time_diff < requestDelay)
    then do
        threadDelay ((requestDelay - time_diff) * 1000000)
        new_time <- getCurrentTime
        res <- do_request
        writeIORef prevRequestTime new_time
        return res
    else do
        res <- do_request
        writeIORef prevRequestTime time
        return res
    where
        do_request = do
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
{-# INLINE read_hex #-}

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

program_size :: Program -> Int
program_size (Lambda x expr) = 1 + expr_size expr
    where
        expr_size (Literal _)         = 1
        expr_size (Id _)              = 1
        expr_size (If0 c t e)         = 1 + expr_size c + expr_size t + expr_size e
        expr_size (Fold e1 e2 _ _ e3) = 2 + expr_size e1 + expr_size e2 + expr_size e3
        expr_size (Op1 _ arg)         = 1 + expr_size arg
        expr_size (Op2 _ arg1 arg2)   = 1 + expr_size arg1 + expr_size arg2

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

----- RealProblem

---- problem typeclass

class Problem a where
    problemId :: a -> String
    problemSize :: a -> Int
    problemOperators :: a -> [HintOp]


---- hints, problem datatype

data HintOp = HintOp1 Op1
            | HintOp2 Op2
            | HintIf0
            | HintTFold
            | HintFold
            | HintBonus
            deriving (Show, Eq, Read)

hint_is_op1, hint_is_op2 :: HintOp -> Bool
hint_is_op1 (HintOp1 _) = True
hint_is_op1 _           = False
hint_is_op2 (HintOp2 _) = True
hint_is_op2 _           = False


data RealProblem = RealProblem
                 { realProblemId :: String
                 , realProblemSize :: Int
                 , realProblemOperators :: [HintOp]
                 , realProblemSolved :: Maybe Bool
                 , realProblemTimeLeft :: Maybe Float
                 }
                 deriving (Show, Eq, Read)

instance Problem RealProblem where
    problemId        = realProblemId
    problemSize      = realProblemSize
    problemOperators = realProblemOperators

problem_store = "/home/sergey/projects/icfpc/2013_Aug/haskell/problems.store"

load_problems :: IO [RealProblem]
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
            "bonus" -> pure HintBonus
            _       -> mplus (fmap HintOp1 $ (parseJSON str)) (fmap HintOp2 $ (parseJSON str))
    parseJSON _          = mzero

instance FromJSON RealProblem where
    parseJSON (Object v) =
        RealProblem <$>
        (v .: "id") <*>
        (v .: "size") <*>
        (v .: "operators") <*>
        (v .:? "solved") <*>
        (v .:? "timeLeft")
    parseJSON invalid = error $ "invalid json when reading Problem: " ++ show invalid

---- Get problems request

get_problems :: IO (Either String [RealProblem])
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

data EvalRequest = EvalId Id [Word64]
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
    parseJSON invalid = error $ "invalid json when reading EvalResponse" ++ (show invalid)

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

data GuessRequest = GuessRequest String Program
                  deriving (Eq, Show)

instance ToJSON GuessRequest where
    toJSON (GuessRequest id program) =
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
    parseJSON invalid = error $ "invalid json when reading GuessResponse" ++ (show invalid)

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

----- Training

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


problem1 = (TrainingProblem
         { trainingChallenge = Lambda "x_7987" (Fold (Id "x_7987") (Literal 0) "x_7987" "x_7988" (Op2 Or (Op2 Plus (Literal 1) (Id "x_7988")) (Id "x_7987")))
         , trainingId = "koc0i0CB42k6WnlWLoCst5Bo"
         , trainingSize = 10
         , trainingOperators = [HintOp2 Or, HintOp2 Plus, HintTFold]})

problem2 = (TrainingProblem
         { trainingChallenge = Lambda "x_11254" (Op1 Shr16 (If0 (Op2 Xor (Op2 Xor (Id "x_11254") (Literal 1)) (Op1 Not (Literal 1))) (Literal 1) (Id "x_11254")))
         , trainingId = "VpUbkJaEDozcYPTsu5t5turv"
         , trainingSize = 11
         , trainingOperators = [HintIf0, HintOp1 Not, HintOp1 Shr16, HintOp2 Xor]})

problem3 = (TrainingProblem
         { trainingChallenge = Lambda "x_18428" (Op1 Shr (Op2 Xor (Id "x_18428") (Op2 And (If0 (Op2 And (Op1 Shl (Op2 Plus (Id "x_18428") (Id "x_18428"))) (Id "x_18428")) (Id "x_18428") (Literal 0)) (Id "x_18428"))))
         , trainingId = "zk42I7MFWlqxIRYZiP3QDPY0"
         , trainingSize = 15
         , trainingOperators = [HintOp2 And, HintIf0, HintOp2 Plus, HintOp1 Shl, HintOp1 Shr, HintOp2 Xor]})

problem4 = (TrainingProblem
         { trainingChallenge = Lambda "x_18436" (Op2 Plus (Op1 Not (Op2 Xor (If0 (Op2 Plus (Op2 Or (Op1 Shr4 (Literal 1)) (Literal 1)) (Id "x_18436")) (Id "x_18436") (Id "x_18436")) (Id "x_18436"))) (Id "x_18436"))
         , trainingId = "bOaaLMSSuN4dRGG5RdHLb0Bi"
         , trainingSize = 15
         , trainingOperators = [HintIf0, HintOp1 Not, HintOp2 Or, HintOp2 Plus, HintOp1 Shr4, HintOp2 Xor]})

problem5 = (TrainingProblem
         { trainingChallenge = Lambda "x_22186" (Op2 Plus (Op2 Xor (Literal 0) (Op1 Shr4 (Op1 Shr16 (Id "x_22186")))) (Op2 And (If0 (Op1 Not (Op1 Shr4 (Op2 And (Id "x_22186") (Literal 0)))) (Literal 0) (Literal 0)) (Id "x_22186")))
         , trainingId = "gIY84OSbY1YBVf2BK7dDfIQO"
         , trainingSize = 17
         , trainingOperators = [HintOp2 And, HintIf0, HintOp1 Not, HintOp2 Plus, HintOp1 Shr16, HintOp1 Shr4, HintOp2 Xor]})

problem6 = (TrainingProblem
         { trainingChallenge = Lambda "x_21134" (Op1 Shr (If0 (Op2 And (Op2 Or (Op2 And (Op2 Plus (Op1 Shr16 (Op1 Shr (Id "x_21134"))) (Id "x_21134")) (Op1 Shr16 (Id "x_21134"))) (Id "x_21134")) (Id "x_21134")) (Literal 0) (Id "x_21134")))
         , trainingId = "HQefrIe69ETIblnbwZWkThN0"
         , trainingSize = 17
         , trainingOperators = [HintOp2 And, HintIf0, HintOp2 Or, HintOp2 Plus, HintOp1 Shr, HintOp1 Shr16]})

problem7 = (TrainingProblem
         { trainingChallenge = Lambda "x_22153" (Op1 Shr16 (Op1 Shr4 (If0 (Op1 Shl (Op2 Plus (Op2 Plus (Op2 Xor (Op2 Or (Op1 Shr (Id "x_22153")) (Id "x_22153")) (Id "x_22153")) (Literal 0)) (Literal 0))) (Id "x_22153") (Id "x_22153"))))
         , trainingId = "dj7t45qKjbVX9q9WBnAmYMfJ"
         , trainingSize = 17
         , trainingOperators = [HintIf0, HintOp2 Or, HintOp2 Plus, HintOp1 Shl, HintOp1 Shr, HintOp1 Shr16, HintOp1 Shr4, HintOp2 Xor]})

problem8 = (TrainingProblem
         { trainingChallenge = Lambda "x_22308" (Op2 Or (Op2 Xor (Op1 Shl (Op1 Shl (Op2 Or (If0 (Op2 Xor (Op2 Xor (Literal 0) (Id "x_22308")) (Id "x_22308")) (Literal 0) (Literal 0)) (Id "x_22308")))) (Id "x_22308")) (Id "x_22308"))
         , trainingId = "VItyrmRFR5BgwdVLLvkMng69"
         , trainingSize = 17
         , trainingOperators = [HintIf0, HintOp2 Or, HintOp1 Shl, HintOp2 Xor]})

problem9 = TrainingProblem {trainingChallenge = Lambda "x_26568" (Op2 Xor (Literal 1) (Op1 Shr16 (Op1 Not (If0 (Op2 Plus (Op1 Shr (Id "x_26568")) (Op2 Or (Op2 Xor (Op1 Shr16 (Op1 Shl (Op2 Plus (Literal 0) (Id "x_26568")))) (Id "x_26568")) (Id "x_26568"))) (Literal 0) (Id "x_26568"))))), trainingId = "JBwB3u5uhndNbOGVEsrS7r8T", trainingSize = 20, trainingOperators = [HintIf0,HintOp1 Not,HintOp2 Or,HintOp2 Plus,HintOp1 Shl,HintOp1 Shr,HintOp1 Shr16,HintOp2 Xor]}

problem10 = TrainingProblem {trainingChallenge = Lambda "x_27774" (Op1 Shr4 (Op2 Xor (If0 (Op2 And (Id "x_27774") (Op2 Plus (Op2 Plus (Op2 Plus (Op2 And (Op1 Shr (Op1 Shl (Id "x_27774"))) (Id "x_27774")) (Literal 0)) (Id "x_27774")) (Id "x_27774"))) (Literal 1) (Literal 0)) (Id "x_27774"))), trainingId = "ASv4fYPaZVC17bkriAqIhlXB", trainingSize = 20, trainingOperators = [HintOp2 And,HintIf0,HintOp2 Plus,HintOp1 Shl,HintOp1 Shr,HintOp1 Shr4,HintOp2 Xor]}

problem11 = (TrainingProblem
            { trainingChallenge = Lambda "x_50675" (Fold (Op1 Not (Op1 Shr16 (Op2 And (If0 (Op1 Shl (Op1 Shr4 (Op2 Plus (Literal 1) (Id "x_50675")))) (Literal 0) (Literal 0)) (Id "x_50675")))) (Id "x_50675") "x_50676" "x_50677" (Op2 Or (Op1 Shl (Id "x_50677")) (Id "x_50676")))
            , trainingId = "zCmNkqqyBlW2q5BYVGGOx5Pr"
            , trainingSize = 20
            , trainingOperators = [HintOp2 And, HintFold, HintIf0, HintOp1 Not, HintOp2 Or, HintOp2 Plus, HintOp1 Shl, HintOp1 Shr16, HintOp1 Shr4]})

problem12 = TrainingProblem {trainingChallenge = Lambda "x_51443" (Fold (Op2 Plus (Op2 Or (If0 (Op2 And (Op1 Not (Op1 Shr16 (Id "x_51443"))) (Literal 1)) (Literal 0) (Id "x_51443")) (Id "x_51443")) (Literal 1)) (Id "x_51443") "x_51444" "x_51445" (Op2 Plus (Op1 Not (Id "x_51445")) (Id "x_51444"))), trainingId = "LM1n0rntBjmjBO2NAqN7alBw", trainingSize = 20, trainingOperators = [HintOp2 And,HintFold,HintIf0,HintOp1 Not,HintOp2 Or,HintOp2 Plus,HintOp1 Shr16]}

-- challenge id size operators
data TrainingProblem = TrainingProblem
                     { trainingChallenge :: Program
                     , trainingId :: String
                     , trainingSize :: Int
                     , trainingOperators :: [HintOp]
                     }
                     deriving (Eq, Show)

instance Problem TrainingProblem where
    problemId        = trainingId
    problemSize      = trainingSize
    problemOperators = trainingOperators


instance FromJSON TrainingProblem where
    parseJSON (Object v) =
        TrainingProblem <$>
        liftM decodeSexpUnsafe (v .: "challenge") <*>
        (v .: "id") <*>
        (v .: "size") <*>
        (v .: "operators")
    parseJSON invalid = error $ "invalid json when reading TrainingProblem: " ++ show invalid

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

----- program enumeration

pairs_summing_to :: Int -> [(Int, Int)]
pairs_summing_to n = [ (i, n - i) | i <- [1..n-1] ]

triples_summing_to :: Int -> [(Int, Int, Int)]
triples_summing_to n = [ (i, j, n - i - j) | i <- [1 .. n - 2], j <- [1 .. n - i - 1] ]

enumerate_programs :: Int -> [Program]
enumerate_programs n | n < 3 = []
                     | otherwise =
    let top_id = "x"
        m      = n - 1
    in Prelude.map (Lambda top_id) $ enumerate_expressions True [top_id] m
    where
        enumerate_expressions _ _   0 = []
        enumerate_expressions _ ids 1 =
            [Literal 0, Literal 1] ++ Prelude.map Id ids
        enumerate_expressions _ ids n@2 =
            [ Op1 op arg
            | arg <- enumerate_expressions False ids (n - 1)
            , op  <- [Not, Shl, Shr, Shr4, Shr16]
            ]
        enumerate_expressions _ ids n@3 =
            [ Op1 op arg
            | arg <- enumerate_expressions False ids (n - 1)
            , op  <- [Not, Shl, Shr, Shr4, Shr16]
            ] ++
            [ Op2 op arg1 arg2
            | (i, j) <- pairs_summing_to (n - 1)
            , arg1   <- enumerate_expressions False ids i
            , arg2   <- enumerate_expressions False ids j
            , op     <- [And, Or, Xor, Plus]
            ]
        enumerate_expressions _ ids n@4 =
            [ Op1 op arg
            | arg <- enumerate_expressions False ids (n - 1)
            , op  <- [Not, Shl, Shr, Shr4, Shr16]
            ] ++
            [ Op2 op arg1 arg2
            | (i, j) <- pairs_summing_to (n - 1)
            , arg1   <- enumerate_expressions False ids i
            , arg2   <- enumerate_expressions False ids j
            , op     <- [And, Or, Xor, Plus]
            ] ++
            [ If0 c t e
            | (i, j, k) <- triples_summing_to (n - 1)
            , c         <- enumerate_expressions False ids i
            , t         <- enumerate_expressions False ids j
            , e         <- enumerate_expressions False ids k
            ]
        enumerate_expressions use_fold ids n =
            [ Op1 op arg
            | arg <- enumerate_expressions True ids (n - 1)
            , op  <- [Not, Shl, Shr, Shr4, Shr16]
            ] ++
            [ Op2 op arg1 arg2
            | (i, j) <- pairs_summing_to (n - 1)
            , arg1   <- enumerate_expressions True ids i
            , arg2   <- enumerate_expressions True ids j
            , op     <- [And, Or, Xor, Plus]
            ] ++
            [ If0 c t e
            | (i, j, k) <- triples_summing_to (n - 1)
            , c         <- enumerate_expressions True ids i
            , t         <- enumerate_expressions True ids j
            , e         <- enumerate_expressions True ids k
            ] ++
            if use_fold
            then
                let aux1 = "aux1"
                    aux2 = "aux2"
                in [ Fold e1 e2 aux1 aux2 e3
                   | (i, j, k) <- triples_summing_to (n - 2)
                   , e1        <- enumerate_expressions False ids i
                   , e2        <- enumerate_expressions False ids j
                   , e3        <- enumerate_expressions False (aux1: aux2: ids) k
                   ]
            else
                []

orbital :: Program -> Word64 -> Int
orbital prog input = iter 0 ev1 (eval ev1)
    where
        eval x = evaluate prog x

        ev1 = (eval input)
        iter n slow fast | slow == fast = n
                         | n >= 10000   = -1
                         | otherwise    = iter (n + 1) (eval slow) (eval (eval fast))

hinted_enum :: Int -> [HintOp] -> [Program]
hinted_enum n hints =
    let top_id = "x"
        m      = n - 1
    in Prelude.map (Lambda top_id) $ hinted_enum_expr [top_id] m
    where
        fold_arg1 = "aux1"
        fold_arg2 = "aux2"

        op1s     = map (\ (HintOp1 op) -> op) $ filter hint_is_op1 hints
        op2s     = map (\ (HintOp2 op) -> op) $ filter hint_is_op2 hints
        has_if   = elem HintIf0 hints
        has_fold = elem HintFold hints
        is_tfold = elem HintTFold hints

        hinted_enum_expr :: [Id] -> Int -> [Expression]
        hinted_enum_expr ids n =
            if is_tfold
            then hinted_enum_tfold_expr ids n
            else if has_fold
                then hinted_enum_complex_expr ids n HintBonus -- use bonus as no hint
                else hinted_enum_simple_expr ids n HintBonus -- use bonus as no hint

        hinted_enum_tfold_expr :: [Id] -> Int -> [Expression]
        hinted_enum_tfold_expr ids n
            | n < 5     = []
            | otherwise =
                [ Fold (Id top_id) (Literal 0) top_id fold_arg1 body
                | top_id <- ids
                , body   <- hinted_enum_simple_expr (fold_arg1: ids) (n - 4) HintTFold
                ]

        hinted_enum_complex_expr :: [Id] -> Int -> HintOp -> [Expression]
        hinted_enum_complex_expr ids n hint
            | n < 5     = hinted_enum_simple_expr ids n hint
            | otherwise =
                make_exprs ids n hinted_enum_complex_expr ++
                [ Fold e1 e2 fold_arg1 fold_arg2 e3
                | (i, j, k) <- triples_summing_to (n - 2)
                , e1        <- hinted_enum_simple_expr ids i HintFold
                , e2        <- hinted_enum_simple_expr ids j HintFold
                , e3        <- hinted_enum_simple_expr (fold_arg1: fold_arg2: ids) k HintFold
                ]

        hinted_enum_simple_expr :: [Id] -> Int -> HintOp -> [Expression]
        hinted_enum_simple_expr ids 0 _ = []
        hinted_enum_simple_expr ids 1 (HintOp1 Shl)   = [Literal 1] ++ Prelude.map Id ids
        hinted_enum_simple_expr ids 1 (HintOp1 Shr)   = [Literal 1] ++ Prelude.map Id ids
        hinted_enum_simple_expr ids 1 (HintOp1 Shr4)  = [Literal 1] ++ Prelude.map Id ids
        hinted_enum_simple_expr ids 1 (HintOp1 Shr16) = [Literal 1] ++ Prelude.map Id ids
        hinted_enum_simple_expr ids 1 (HintOp2 And)   = Prelude.map Id ids
        hinted_enum_simple_expr ids 1 (HintOp2 Or)    = Prelude.map Id ids
        hinted_enum_simple_expr ids 1 (HintOp2 Xor)   = [Literal 1] ++ Prelude.map Id ids
        hinted_enum_simple_expr ids 1 (HintOp2 Plus)  = [Literal 1] ++ Prelude.map Id ids
        hinted_enum_simple_expr ids 1 _ = [Literal 0, Literal 1] ++ Prelude.map Id ids
        hinted_enum_simple_expr ids n _ = make_exprs ids n hinted_enum_simple_expr

        make_exprs :: [Id] -> Int -> ([Id] -> Int -> HintOp -> [Expression]) -> [Expression]
        make_exprs ids n make_subexps = iter 1
            where
                iter m | m > n     = []
                       | otherwise =
                           [Literal 0, Literal 1] ++ Prelude.map Id ids ++
                           [ Op1 op arg
                           | op  <- op1s
                           , arg <- make_subexps ids (m - 1) (HintOp1 op)
                           ] ++
                           [ Op2 op arg1 arg2
                           | (i, j) <- pairs_summing_to (m - 1)
                           , op     <- op2s
                           , arg1   <- make_subexps ids i (HintOp2 op)
                           , arg2   <- make_subexps ids j (HintOp2 op)
                           ] ++
                           [ If0 c t e
                           | (i, j, k) <- triples_summing_to (m - 1)
                           , c <- make_subexps ids i HintIf0
                           , t <- make_subexps ids j HintIf0
                           , e <- make_subexps ids k HintIf0
                           ] ++
                           iter (m + 1)

-- returns false if this expression can never yield such output
-- input is omitted deliberately
check_toplevel_expr_consistency_fast :: Expression -> Word64 -> Bool
check_toplevel_expr_consistency_fast (Op1 Shl _)   output = not $ testBit output 0
check_toplevel_expr_consistency_fast (Op1 Shr _)   output = not $ testBit output 63
check_toplevel_expr_consistency_fast (Op1 Shr4 _)  output = output .&. 0xf000000000000000 == 0x0000000000000000
check_toplevel_expr_consistency_fast (Op1 Shr16 _) output = output .&. 0xffff000000000000 == 0x0000000000000000
check_toplevel_expr_consistency_fast _             _      = True


enum_problem :: (Problem p) => p -> [Program]
enum_problem p = hinted_enum (problemSize p) (problemOperators p)

debug x = putStrLn x

inputs_at_a_time :: Int
inputs_at_a_time = 256

solve_problem :: (Problem p) => p -> IO ()
solve_problem p = do
    let progs  = enum_problem p
        inputs = Prelude.take inputs_at_a_time [0..]
    debug "doing initial eval"
    resp <- eval_request $! EvalId (problemId p) inputs
    case resp of
        Left msg -> do
            printf "error while doing initial eval request: %s\n" msg
        Right (EvalError msg) -> do
            printf "eval error while doing initial eval request: %s\n" msg
        Right (EvalOk outputs) -> do
            debug "initial eval ok"
            iter progs (zip inputs outputs) (IS.fromList $! map fromIntegral inputs)
    where

        check_prog prog@(Lambda _ expr) io_pairs =
            all (\(input, output) -> check_toplevel_expr_consistency_fast expr output &&
                    output == evaluate prog input)
                io_pairs
        iter :: [Program] -> [(Word64, Word64)] -> IS.IntSet -> IO ()
        iter progs io_pairs input_set = do
            let !(candidate_prog: progs_rest) =
                    filter (\p -> check_prog p io_pairs) progs
            debug $ printf "doing guess with program %s" (encodeSexp candidate_prog)
            resp <- guess_request $! GuessRequest (problemId p) candidate_prog
            case resp of
                Left msg -> do
                    printf "error while doing guess request: %s\n" msg
                Right (GuessError msg) -> do
                    printf "error while doing guess request: %s\n" msg
                Right (GuessWin) -> do
                    printf "guessed correctly: %s\n" (encodeSexp candidate_prog)
                Right (GuessMismatch new_input res our_res) -> do
                    debug "guess mismatch"
                    -- reps <- eval_request $! EvalId (problemId p) input_set
                    let input_set' = IS.insert (fromIntegral $ read_hex new_input) input_set
                    (more_inputs, input_set'') <- generateInputs input_set'
                    debug "doing eval to clarify matters"
                    eval_resp <- eval_request $! EvalId (problemId p) more_inputs
                    case eval_resp of
                        Left msg -> do
                            printf "error while doing eval request: %s\n" msg
                        Right (EvalError msg) -> do
                            printf "eval error while doing eval request: %s\n" msg
                        Right (EvalOk outputs) -> do
                            debug "iterating further"
                            -- let new_pairs =
                            --         zip more_inputs outputs ++ (read_hex new_input, read_hex res): io_pairs
                            let new_pairs =
                                    (read_hex new_input, read_hex res): zip more_inputs outputs
                            progs_rest `seq` iter progs_rest new_pairs input_set''

generateInputs :: IS.IntSet -> IO ([Word64], IS.IntSet)
generateInputs input_set = do
    gen <- getStdGen
    let (!new_inputs, !input_set', !new_gen) = generate inputs_at_a_time gen input_set []
    setStdGen new_gen
    return (new_inputs, input_set')
    where
        input_range :: (Word64, Word64)
        input_range = (0x0000000000000000, 0xffffffffffffffff)

        generate :: (RandomGen g) => Int -> g -> IS.IntSet -> [Word64] -> ([Word64], IS.IntSet, g)
        generate 0 !gen !inp !generated_inputs =
            (generated_inputs, inp, gen)
        generate !n !gen !inp !generated_inputs =
            let (sample, gen') = randomR input_range gen
                sample'        = fromIntegral sample :: Int
            in if IS.member sample' inp
                then generate n gen' inp generated_inputs
                else generate (n - 1) gen' (IS.insert sample' inp) (sample: generated_inputs)

main :: IO ()
main = do
    -- mapM_ (\(p, orb) -> putStrLn (encodeSexp p) >> printf "orbital = %d\n" orb) $
    --     sortBy (\(_, orb1) (_, orb2) -> compare orb1 orb2) $
    --     Prelude.filter (\(_, orb) -> orb /= 0) $
    --     Prelude.map (\p -> (p, orbital p 1)) $
    --     enumerate_programs 7

    let problem = problem12
    printf "size = %d, # of operators = %d\n" (problemSize problem) (length $ problemOperators problem)
    start <- getCurrentTime
    solve_problem problem
    end <- getCurrentTime
    printf "answer = %s\n" (encodeSexp $ trainingChallenge problem)
    printf "duration = %s\n" (show $ diffUTCTime end start)

    -- problems <- load_problems
    -- mapM_ (\p -> printf "size = %d, hint length = %d, hint = %s\n" (problemSize p) (length $ problemOperators p) (show $ problemOperators p) >> printf "# of programs = %d\n" (length $ enum_problem p)) $
    --     sortBy (\p1 p2-> compare (length (problemOperators p1) + problemSize p1) (length (problemOperators p2) + problemSize p2)) $
    --     -- filter (\p -> not $ elem HintFold $ problemOperators p) $
    --     problems

    -- training_request (TrainingRequest 3 RequestNoOperator) >>= print

