-----------------------------------------------------------------------------------------------
-- |
-- Module      :  Test
-- Copyright   :  (c) Sergey Vinokurov 2013
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
-----------------------------------------------------------------------------------------------

module Test where

import Main

import Test.HUnit
import Text.Printf

import Data.Aeson (encode, decode, decode')
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.ByteString.Char8 as SBS

import Data.HashMap.Strict as HM


----- Reading/writing I/O

---- Program: reading from JSON

test_problem_read1 =
    let input = BS.pack "{\"id\":\"dKdeIAoZMyb5y3a74iTcLXyr\", \"size\":30, \"operators\":[\"shr16\",\"if0\",\"xor\",\"plus\",\"not\",\"fold\"]}"
        hints = [ HintOp1 Shr16
                , HintIf0
                , HintOp2 Xor
                , HintOp2 Plus
                , HintOp1 Not
                , HintFold ]
        result = Just $ Problem "dKdeIAoZMyb5y3a74iTcLXyr" 30 hints Nothing Nothing
    in TestCase $ (assertEqual "" result (decode' input))

test_problem_read2 =
    let input = BS.pack "{\"id\":\"hx2XLtS756IvDv9ZNuILizxJ\", \"size\":3, \"operators\":[\"not\"], \"solved\":true, \"timeLeft\":0}"

        hints = [HintOp1 Not]
        result = Just $ Problem "hx2XLtS756IvDv9ZNuILizxJ" 3 hints (Just True) (Just 0)
    in TestCase $ (assertEqual "" result (decode' input))

reading_tests :: Test
reading_tests = TestList [ test_problem_read1, test_problem_read2
                           {-TestLabel "test_problem_read1" test_problem_read1-}
                         ]

---- writing

test_write_guess1 =
    let input = Guess "afa696afglajf696af" (Lambda "x" (Op2 Plus (Id "x") (Literal 1)))
        result = "{\"program\":\"(lambda (x) (plus x 1))\",\"id\":\"afa696afglajf696af\"}"
    in TestCase $ (assertEqual "write_guess1" result (BS.unpack $ encode input))

test_write_eval_request1 =
    let input = EvalProgram (Lambda "x" (Op1 Shl (Id "x"))) [0x00000000000001, 0xEFFFFFFFFFFFFF]
        result = "{\"program\":\"(lambda (x) (shl1 x))\",\"arguments\":[\"0x1\",\"0xefffffffffffff\"]}"
    in TestCase $ (assertEqual "write_eval_request1" esult (BS.unpack $ encode input))

writing_tests :: Test
writing_tests = TestList [test_write_guess1, test_write_eval_request1]

-- [
--      {"id":"dKdeIAoZMyb5y3a74iTcLXyr",
--       "size":30,
--       "operators":["shr16","if0","xor","plus","not","fold"]},
--      {"id":"hx2XLtS756IvDv9ZNuILizxJ",
--       "size":3,
--       "operators":["not"],
--       "solved":true,
--       "timeLeft":0},
--      {"id":"af82718a7fhla74cal8faf7a",
--       "size":3,
--       "operators":["not"],
--       "timeLeft":192.61}
--     ]


-- "[ {\"id\":\"dKdeIAoZMyb5y3a74iTcLXyr\", \"size\":30, \"operators\":[\"shr16\",\"if0\",\"xor\",\"plus\",\"not\",\"fold\"]}, {\"id\":\"hx2XLtS756IvDv9ZNuILizxJ\", \"size\":3, \"operators\":[\"not\"], \"solved\":true, \"timeLeft\":0}, {\"id\":\"af82718a7fhla74cal8faf7a\", \"size\":3, \"operators\":[\"not\"], \"timeLeft\":192.61} ]"

----- Sexp I/O
---- Sexp writing

program_cases = [ ("(lambda (foo) foo)"
                  , Lambda "foo" (Id "foo"))
                , ("(lambda (foo) (if0 foo 0 1))"
                  , Lambda "foo" (If0 (Id "foo") (Literal 0) (Literal 1)))
                , ("(lambda (foo) (fold foo (xor foo 1) (lambda (a b) (xor (not a) b))))"
                  , Lambda "foo" (Fold (Id "foo")
                                 (Op2 Xor (Id "foo") (Literal 1))
                                 "a"
                                 "b"
                                 (Op2 Xor (Op1 Not (Id "a")) (Id "b"))))
                , ("(lambda (bar_023) (xor bar_023 (plus (xor bar_023 1) (shr16 (shl1 (shr4 1))))))"
                  , Lambda "bar_023" (Op2 Xor
                                          (Id "bar_023")
                                          (Op2 Plus
                                               (Op2 Xor
                                                    (Id "bar_023")
                                                    (Literal 1))
                                               (Op1 Shr16
                                                    (Op1 Shl
                                                         (Op1 Shr4
                                                              (Literal 1)))))))
                ]

make_write_case msg id =
    let (str, prog) = program_cases !! id
    in TestCase $ (assertEqual msg str (encodeSexp prog))

program_to_sexp_writing_tests :: Test
program_to_sexp_writing_tests =
    TestList [make_write_case (printf "write%d" id) id | id <- [0..length program_cases - 1]]

---- Sexp reading

make_read_case msg id =
    let (str, prog) = program_cases !! id
    in TestCase $ (assertEqual (msg ++ ": " ++ str) (Right prog) (decodeSexp $ SBS.pack str))


sexp_to_program_reading_tests :: Test
sexp_to_program_reading_tests =
    TestList [make_read_case (printf "read%d" id) id | id <- [0..length program_cases - 1]]

----- eval

test_eval1 = TestCase $ assertEqual "" 0 (eval (Literal 0) HM.empty)
test_eval2 = TestCase $ assertEqual "" 1 (eval (Literal 1) HM.empty)
test_eval3 = TestCase $ assertEqual "" 101 (eval (Id "x") $ HM.singleton "x" 101)
test_eval4 = TestCase $ assertEqual "" 101 (eval (If0 (Literal 0) (Id "x") (Literal 1)) $ HM.singleton "x" 101)
test_eval5 = TestCase $ assertEqual "" 1 (eval (If0 (Literal 1) (Id "x") (Literal 1)) $ HM.singleton "x" 101)

test_not1 = TestCase $ assertEqual "" 0xFFFFFFFFFFFFFFFF (eval (Op1 Not (Literal 0)) HM.empty)
test_not2 = TestCase $ assertEqual "" 0xFFFFFFFFFFFFFFFE (eval (Op1 Not (Literal 1)) HM.empty)
test_not3 = TestCase $ assertEqual "" 0x00000000FFFFFFFF (eval (Op1 Not (Literal 0xFFFFFFFF00000000)) HM.empty)

test_shift1 = TestCase $ assertEqual "shift1" 0 (eval (Op1 Shl (Literal 0)) HM.empty)
test_shift2 = TestCase $ assertEqual "shift2" 2 (eval (Op1 Shl (Literal 1)) HM.empty)
test_shift3 = TestCase $ assertEqual "shift3" 4 (eval (Op1 Shl (Op1 Shl (Literal 1))) HM.empty)
test_shift4 = TestCase $ assertEqual "shift4" 1 (eval (Op1 Shr (Op1 Shl (Literal 1))) HM.empty)
test_shift5 = TestCase $ assertEqual "shift5" 0x0FF00000000000 (eval (Op1 Shr4 (Literal 0xFF000000000000)) HM.empty)
test_shift6 = TestCase $ assertEqual "shift6" 0x0000FF00000000 (eval (Op1 Shr16 (Literal 0xFF000000000000)) HM.empty)


decodeUnsafe :: String -> Program
decodeUnsafe input = either (\_ -> error "should not happen in tests") id $ decodeSexp' input

test_fold1 =
    let prog = "(lambda (x) (fold x 0 (lambda (y z) (or y z))))"
        input = 0x1122334455667788
    in TestCase $ assertEqual "" 0x00000000000000FF (evaluate (decodeUnsafe prog) input)

test_fold2 =
    let prog = "(lambda (x) (fold x 0 (lambda (y z) (plus y z))))"
        input = 0x0101010101010101
    in TestCase $ assertEqual "" 0x0000000000000008 (evaluate (decodeUnsafe prog) input)

test_fold3 =
    let prog = "(lambda (x) (fold x 0 (lambda (y z) (plus y z))))"
        input = 0x0404040404040404
    in TestCase $ assertEqual "" 0x0000000000000020 (evaluate (decodeUnsafe prog) input)

test_fold4 =
    let prog = "(lambda (x) (fold x 1 (lambda (y z) (and y z))))"
        input = 0x0404040404040404
    in TestCase $ assertEqual "" 0x0000000000000000 (evaluate (decodeUnsafe prog) input)


eval_tests :: Test
eval_tests =
    TestList [ test_eval1, test_eval2, test_eval3, test_eval4, test_eval5,
               test_shift1, test_shift2, test_shift3, test_shift4, test_shift5, test_shift6,
               test_not1, test_not2, test_not3,
               test_fold1, test_fold2, test_fold3, test_fold4
             ]

---- test utils

read_hex_tests = [ (0, "0")
                 , (15, "f")
                 , (15, "0xf")
                 , (255, "0xff")
                 , (256, "0x100")
                 , (10, "a")
                 ]

args_to_hex_tests = [ (["0x0"], [0])
                    , (["0x0", "0x1"], [0, 1])
                    , (["0x0", "0x1", "0xff"], [0, 1, 0xff])
                    , (["0xffffffffffffffff"], [0xffffffffffffffff])
                    ]

util_tests :: Test
util_tests =
    TestList $ [TestCase $ assertEqual "" res (read_hex str) | (res, str) <- read_hex_tests] ++
               [TestCase $ assertEqual "" res (args_to_hex input) | (res, input) <- args_to_hex_tests]



----- main

main :: IO ()
main = do
    runTestTT reading_tests
    runTestTT writing_tests
    runTestTT program_to_sexp_writing_tests
    runTestTT sexp_to_program_reading_tests
    runTestTT eval_tests
    runTestTT util_tests
    return ()


