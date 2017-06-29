{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-} -- For equational constraints

module DebuggerTest where

import Testing
import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Debugger
import Control.Hspl.Internal.Solver

import Data.List
import Data.Monoid ((<>))
import Data.Time.Clock
import System.Directory
import System.FilePath

runTest :: Goal -> [String] -> [String] -> IO ()
runTest g commands expectedOutput = do
  tmp <- getTemporaryDirectory

  UTCTime { utctDayTime=ts } <- getCurrentTime

  let config = debugConfig { inputFile = tmp </> "hspl-test-" ++ show ts ++ ".in"
                           , outputFile = tmp </> "hspl-test-" ++ show ts ++ ".out"
                           , interactive = False
                           , coloredOutput = False
                           }
  writeFile (inputFile config) $ unlines commands
  debug config g
  actualOutput <- readFile $ outputFile config
  removeFile $ inputFile config
  removeFile $ outputFile config
  actualOutput `shouldEqual` unlines expectedOutput

expectTrace :: TermData a => String -> Int -> String -> a -> String
expectTrace s d pred arg = "(" ++ show d ++ ") " ++ s ++ ": " ++ show (predicate pred arg)

expectCall :: TermData a => Int -> String -> a -> String
expectCall = expectTrace "Call"

expectRedo :: TermData a => Int -> String -> a -> String
expectRedo = expectTrace "Redo"

expectExit :: TermData a => Int -> String -> a -> String
expectExit = expectTrace "Exit"

expectFail :: TermData a => Int -> String -> a -> String
expectFail = expectTrace "Fail"

expectUnknownPred :: TermData a => Int -> String -> a -> String
expectUnknownPred d pred arg = "(" ++ show d ++ ") Error: Unknown predicate \"" ++
                                pred ++ " :: " ++ show (predType $ predicate pred arg) ++ "\""

expectCanUnifyCall :: (TermData a, TermData b, HSPLType a ~ HSPLType b) =>
                        Int -> a -> b -> String
expectCanUnifyCall d t1 t2 = "(" ++ show d ++ ") Call: " ++ show (CanUnify (toTerm t1) (toTerm t2))

expectCanUnifyExit :: (TermData a) => Int -> a -> String
expectCanUnifyExit d t = "(" ++ show d ++ ") Exit: " ++ show (CanUnify (toTerm t) (toTerm t))

expectCanUnifyFail :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => Int -> a -> b -> String
expectCanUnifyFail d t1 t2 = "(" ++ show d ++ ") Fail: " ++ show (CanUnify (toTerm t1) (toTerm t2))

expectIdenticalCall :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => Int -> a -> b -> String
expectIdenticalCall d t1 t2 = "(" ++ show d ++ ") Call: " ++ show (Identical (toTerm t1) (toTerm t2))

expectIdenticalExit :: (TermData a) => Int -> a -> String
expectIdenticalExit d t = "(" ++ show d ++ ") Exit: " ++ show (Identical (toTerm t) (toTerm t))

expectIdenticalFail :: (TermData a, TermData b, HSPLType a ~ HSPLType b) =>
                        Int -> a -> b -> String
expectIdenticalFail d t1 t2 = "(" ++ show d ++ ") Fail: " ++ show (Identical (toTerm t1) (toTerm t2))

expectEqualCall :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => Int -> a -> b -> String
expectEqualCall d a b = "(" ++ show d ++ ") Call: " ++ show (Equal (toTerm a) (toTerm b))

expectEqualExit :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => Int -> a -> b -> String
expectEqualExit d a b = "(" ++ show d ++ ") Exit: " ++ show (Equal (toTerm a) (toTerm b))

expectEqualFail :: (TermData a, TermData b, HSPLType a ~ HSPLType b) => Int -> a -> b -> String
expectEqualFail d a b = "(" ++ show d ++ ") Fail: " ++ show (Equal (toTerm a) (toTerm b))

expectLessThanCall :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Ord (HSPLType a)) =>
                      Int -> a -> b -> String
expectLessThanCall d a b = "(" ++ show d ++ ") Call: " ++ show (LessThan (toTerm a) (toTerm b))

expectLessThanExit :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Ord (HSPLType a)) =>
                      Int -> a -> b -> String
expectLessThanExit d a b = "(" ++ show d ++ ") Exit: " ++ show (LessThan (toTerm a) (toTerm b))

expectLessThanFail :: (TermData a, TermData b, HSPLType a ~ HSPLType b, Ord (HSPLType a)) =>
                      Int -> a -> b -> String
expectLessThanFail d a b = "(" ++ show d ++ ") Fail: " ++ show (LessThan (toTerm a) (toTerm b))

expectNotCall :: Int -> Goal -> String
expectNotCall d g = "(" ++ show d ++ ") Call: " ++ show (Not g)

expectNotExit :: Int -> Goal -> String
expectNotExit d g = "(" ++ show d ++ ") Exit: " ++ show (Not g)

expectNotFail :: Int -> Goal -> String
expectNotFail d g = "(" ++ show d ++ ") Fail: " ++ show (Not g)

expectAndCall :: Int -> Goal -> Goal -> String
expectAndCall d g1 g2 = "(" ++ show d ++ ") Call: " ++ show (And g1 g2)

expectAndExit :: Int -> Goal -> Goal -> String
expectAndExit d g1 g2 = "(" ++ show d ++ ") Exit: " ++ show (And g1 g2)

expectAndFail :: Int -> Goal -> Goal -> String
expectAndFail d g1 g2 = "(" ++ show d ++ ") Fail: " ++ show (And g1 g2)

expectOrCall :: Int -> Goal -> Goal -> String
expectOrCall d g1 g2 = "(" ++ show d ++ ") Call: " ++ show (Or g1 g2)

expectOrRedo :: Int -> Goal -> Goal -> String
expectOrRedo d g1 g2 = "(" ++ show d ++ ") Redo: " ++ show (Or g1 g2)

expectOrExit :: Int -> Goal -> Goal -> String
expectOrExit d g1 g2 = "(" ++ show d ++ ") Exit: " ++ show (Or g1 g2)

expectOrFail :: Int -> Goal -> Goal -> String
expectOrFail d g1 g2 = "(" ++ show d ++ ") Fail: " ++ show (Or g1 g2)

expectTop :: Int -> [String]
expectTop d = [ "(" ++ show d ++ ") Call: " ++ show Top
              , "(" ++ show d ++ ") Exit: " ++ show Top
              ]

expectBottom :: Int -> [String]
expectBottom d = [ "(" ++ show d ++ ") Call: " ++ show Bottom
                 , "(" ++ show d ++ ") Fail: " ++ show Bottom
                 ]

expectAlternativesCall :: (TermData a, TermData as, HSPLType as ~ [HSPLType a]) =>
                          Int -> a -> Goal -> as -> String
expectAlternativesCall d x g xs = "(" ++ show d ++ ") Call: " ++
                                  show (Alternatives (toTerm x) g (toTerm xs))

expectAlternativesExit :: (TermData a, TermData as, HSPLType as ~ [HSPLType a]) =>
                          Int -> a -> Goal -> as -> String
expectAlternativesExit d x g xs = "(" ++ show d ++ ") Exit: " ++
                                  show (Alternatives (toTerm x) g (toTerm xs))

expectAlternativesFail :: (TermData a, TermData as, HSPLType as ~ [HSPLType a]) =>
                          Int -> a -> Goal -> as -> String
expectAlternativesFail d x g xs = "(" ++ show d ++ ") Fail: " ++
                                  show (Alternatives (toTerm x) g (toTerm xs))

-- deep(X) :- foo(X).
-- foo(X) :- bar(X).
-- bar(a).
deep = [ HornClause (predicate "deep" (Var "x" :: Var Char))
                    (PredGoal (predicate "foo" (Var "x" :: Var Char))
                              [HornClause (predicate "foo" (Var "x" :: Var Char))
                                                (PredGoal (predicate "bar" (Var "x" :: Var Char))
                                                          [HornClause (predicate "bar" 'a') Top])])
       ]

-- wide(X, Y, Z) :- foo(X), bar(Y), baz(Z).
-- foo(a).
-- bar(b).
-- baz(c).
wide = [ HornClause (  predicate "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char))
                    (  PredGoal (predicate "foo" (Var "x" :: Var Char))
                                [HornClause (predicate "foo" 'a') Top]
                    <> PredGoal (predicate "bar" (Var "y" :: Var Char))
                                [HornClause (predicate "bar" 'b') Top]
                    <> PredGoal (predicate "baz" (Var "z" :: Var Char))
                                [HornClause (predicate "baz" 'c') Top]
                    )
       ]

-- foo(X) :-
--   bar(X) % Undefined predicate
--   baz(a) % Predicate that fails on input 'a'
-- baz(b).
backtracking = [ HornClause (predicate "foo" (Var "x" :: Var Char))
                            (PredGoal (predicate "bar" (Var "x" :: Var Char)) [])
               , HornClause (predicate "foo" (Var "x" :: Var Char))
                            (PredGoal (predicate "baz" 'a')
                                      [HornClause (predicate "baz" 'b') Top])
               ]

test = describeModule "Control.Hspl.Internal.Debugger" $ do
  describe "the step command" $ do
    let deepGoal = PredGoal (predicate "deep" (Var "x" :: Var Char)) deep
    let deepTrace = [ expectCall 1 "deep" (Var "x" :: Var Char)
                    , expectCall 2 "foo" (Var "x" :: Var Char)
                    , expectCall 3 "bar" (Var "x" :: Var Char)
                    , expectExit 3 "bar" 'a'
                    , expectExit 2 "foo" 'a'
                    , expectExit 1 "deep" 'a'
                    ]
    let wideGoal = PredGoal (predicate "wide"
                      (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide
    let wideTrace = [ expectCall 1 "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
                    , expectCall 2 "foo" (Var "x" :: Var Char)
                    , expectExit 2 "foo" 'a'
                    , expectCall 2 "bar" (Var "y" :: Var Char)
                    , expectExit 2 "bar" 'b'
                    , expectCall 2 "baz" (Var "z" :: Var Char)
                    , expectExit 2 "baz" 'c'
                    , expectExit 1 "wide" ('a', 'b', 'c')
                    ]
    let backtrackingGoal = PredGoal (predicate "foo" (Var "x" :: Var Char)) backtracking
    let backtrackingTrace = [ expectCall 1 "foo" (Var "x" :: Var Char)
                            , expectCall 2 "bar" (Var "x" :: Var Char)
                            , expectUnknownPred 2 "bar" (Var "x" :: Var Char)
                            , expectFail 1 "foo" (Var "x" :: Var Char)
                            , expectRedo 1 "foo" (Var "x" :: Var Char)
                            , expectCall 2 "baz" 'a'
                            , expectFail 2 "baz" 'a'
                            , expectFail 1 "foo" (Var "x" :: Var Char)
                            ]
    let canUnifyGoal = CanUnify (toTerm (Var "x" :: Var String)) (toTerm "foo")
    let canUnifyTrace = [ expectCanUnifyCall 1 (Var "x" :: Var String) "foo"
                        , expectCanUnifyExit 1 "foo"
                        ]
    let canUnifyFailGoal = CanUnify (toTerm "bar") (toTerm "foo")
    let canUnifyFailTrace = [ expectCanUnifyCall 1 "bar" "foo"
                            , expectCanUnifyFail 1 "bar" "foo"
                            ]
    let identicalGoal = Identical (toTerm "foo") (toTerm "foo")
    let identicalTrace = [ expectIdenticalCall 1 "foo" "foo"
                         , expectIdenticalExit 1 "foo"
                         ]
    let identicalFailGoal = Identical (toTerm (Var "x" :: Var String)) (toTerm "foo")
    let identicalFailTrace = [ expectIdenticalCall 1 (Var "x" :: Var String) "foo"
                             , expectIdenticalFail 1 (Var "x" :: Var String) "foo"
                             ]
    let equalGoal = Equal (toTerm (Var "x" :: Var Int)) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
    let equalTrace = [ expectEqualCall 1 (Var "x" :: Var Int) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
                     , expectEqualExit 1 (3 :: Int) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
                     ]
    let equalFailGoal = Equal (toTerm (2 :: Int)) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
    let equalFailTrace = [ expectEqualCall 1 (2 :: Int) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
                         , expectEqualFail 1 (2 :: Int) (Sum (toTerm (1 :: Int)) (toTerm (2 :: Int)))
                         ]
    let lessThanGoal = LessThan (Sum (toTerm (2 :: Int)) (toTerm (3 :: Int)))
                                (Product (toTerm (2 :: Int)) (toTerm (3 :: Int)))
    let lessThanTrace = [ expectLessThanCall 1 (Sum (toTerm (2 :: Int)) (toTerm (3 :: Int)))
                                               (Product (toTerm (2 :: Int)) (toTerm (3 :: Int)))
                        , expectLessThanExit 1 (5 :: Int) (6 :: Int)
                        ]
    let lessThanFailGoal = LessThan (Product (toTerm (2 :: Int)) (toTerm (3 :: Int)))
                                     (Sum (toTerm (2 :: Int)) (toTerm (3 :: Int)))
    let lessThanFailTrace = [ expectLessThanCall 1 (Product (toTerm (2 :: Int)) (toTerm (3 :: Int)))
                                                   (Sum (toTerm (2 :: Int)) (toTerm (3 :: Int)))
                            , expectLessThanFail 1 (Product (toTerm (2 :: Int)) (toTerm (3 :: Int)))
                                                   (Sum (toTerm (2 :: Int)) (toTerm (3 :: Int)))
                            ]
    let notGoal = Not $ CanUnify (toTerm "bar") (toTerm "foo")
    let notTrace = [ expectNotCall 1 $ CanUnify (toTerm "bar") (toTerm "foo")
                   , expectCanUnifyCall 2 "bar" "foo"
                   , expectCanUnifyFail 2 "bar" "foo"
                   , expectNotExit 1 $ CanUnify (toTerm "bar") (toTerm "foo")
                   ]
    let notFailGoal = Not $ CanUnify (toTerm (Var "x" :: Var String)) (toTerm "foo")
    let notFailTrace = [ expectNotCall 1 $ CanUnify (toTerm (Var "x" :: Var String)) (toTerm "foo")
                       , expectCanUnifyCall 2 (Var "x" :: Var String) "foo"
                       , expectCanUnifyExit 2 "foo"
                       , expectNotFail 1 $ CanUnify (toTerm (Var "x" :: Var String)) (toTerm "foo")
                       ]
    let andGoal = And (CanUnify (toTerm "foo") (toTerm (Var "x" :: Var String)))
                      (Identical (toTerm "foo") (toTerm (Var "x" :: Var String)))
    let andTrace = [ expectCanUnifyCall 1 "foo" (Var "x" :: Var String)
                   , expectCanUnifyExit 1 "foo"
                   , expectIdenticalCall 1 "foo" "foo"
                   , expectIdenticalExit 1 "foo"
                   ]
    let andFailLeftGoal = And (CanUnify (toTerm "foo") (toTerm "bar"))
                              (Identical (toTerm "foo") (toTerm "foo"))
    let andFailLeftTrace = [ expectCanUnifyCall 1 "foo" "bar"
                           , expectCanUnifyFail 1 "foo" "bar"
                           ]
    let andFailRightGoal = And (Identical (toTerm "foo") (toTerm "foo"))
                               (CanUnify (toTerm "foo") (toTerm "bar"))
    let andFailRightTrace = [ expectIdenticalCall 1 "foo" "foo"
                            , expectIdenticalExit 1 "foo"
                            , expectCanUnifyCall 1 "foo" "bar"
                            , expectCanUnifyFail 1 "foo" "bar"
                            ]
    let orLeftGoal = Or (CanUnify (toTerm "foo") (toTerm "foo"))
                        (CanUnify (toTerm "foo") (toTerm "bar"))
    let orLeftTrace = [ expectOrCall 1 (CanUnify (toTerm "foo") (toTerm "foo"))
                                       (CanUnify (toTerm "foo") (toTerm "bar"))
                      , expectCanUnifyCall 2 "foo" "foo"
                      , expectCanUnifyExit 2 "foo"
                      , expectOrExit 1 (CanUnify (toTerm "foo") (toTerm "foo"))
                                       (CanUnify (toTerm "foo") (toTerm "bar"))
                      , expectOrRedo 1 (CanUnify (toTerm "foo") (toTerm "foo"))
                                       (CanUnify (toTerm "foo") (toTerm "bar"))
                      , expectCanUnifyCall 2 (toTerm "foo") (toTerm "bar")
                      , expectCanUnifyFail 2 (toTerm "foo") (toTerm "bar")
                      , expectOrFail 1 (CanUnify (toTerm "foo") (toTerm "foo"))
                                       (CanUnify (toTerm "foo") (toTerm "bar"))
                      ]
    let orRightGoal = Or (CanUnify (toTerm "bar") (toTerm "foo"))
                         (CanUnify (toTerm "foo") (toTerm "foo"))
    let orRightTrace = [ expectOrCall 1 (CanUnify (toTerm "bar") (toTerm "foo"))
                                        (CanUnify (toTerm "foo") (toTerm "foo"))
                       , expectCanUnifyCall 2 "bar" "foo"
                       , expectCanUnifyFail 2 "bar" "foo"
                       , expectOrFail 1 (CanUnify (toTerm "bar") (toTerm "foo"))
                                        (CanUnify (toTerm "foo") (toTerm "foo"))
                       , expectOrRedo 1 (CanUnify (toTerm "bar") (toTerm "foo"))
                                        (CanUnify (toTerm "foo") (toTerm "foo"))
                       , expectCanUnifyCall 2 "foo" "foo"
                       , expectCanUnifyExit 2 "foo"
                       , expectOrExit 1 (CanUnify (toTerm "bar") (toTerm "foo"))
                                        (CanUnify (toTerm "foo") (toTerm "foo"))
                       ]
    let orFailGoal = Or (CanUnify (toTerm "bar") (toTerm "foo"))
                        (CanUnify (toTerm "foo") (toTerm "baz"))
    let orFailTrace = [ expectOrCall 1 (CanUnify (toTerm "bar") (toTerm "foo"))
                                       (CanUnify (toTerm "foo") (toTerm "baz"))
                      , expectCanUnifyCall 2 "bar" "foo"
                      , expectCanUnifyFail 2 "bar" "foo"
                      , expectOrFail 1 (CanUnify (toTerm "bar") (toTerm "foo"))
                                       (CanUnify (toTerm "foo") (toTerm "baz"))
                      , expectOrRedo 1 (CanUnify (toTerm "bar") (toTerm "foo"))
                                       (CanUnify (toTerm "foo") (toTerm "baz"))
                      , expectCanUnifyCall 2 "foo" "baz"
                      , expectCanUnifyFail 2 "foo" "baz"
                      , expectOrFail 1 (CanUnify (toTerm "bar") (toTerm "foo"))
                                       (CanUnify (toTerm "foo") (toTerm "baz"))
                      ]
    let alternativesGoal = Alternatives (toTerm (Var "x" :: Var Char))
                                        (Or (CanUnify (toTerm $ Var "x") (toTerm 'a'))
                                            (CanUnify (toTerm $ Var "x") (toTerm 'b')))
                                        (toTerm $ Var "xs")
    let alternativesTrace = [ expectAlternativesCall 1 (Var "x" :: Var Char)
                                                       (Or (CanUnify (toTerm $ Var "x") (toTerm 'a'))
                                                           (CanUnify (toTerm $ Var "x") (toTerm 'b')))
                                                       (Var "xs")
                            , expectOrCall 2 (CanUnify (toTerm $ Var "x") (toTerm 'a'))
                                             (CanUnify (toTerm $ Var "x") (toTerm 'b'))
                            , expectCanUnifyCall 3 (Var "x") 'a'
                            , expectCanUnifyExit 3 'a'
                            , expectOrExit 2 (CanUnify (toTerm 'a') (toTerm 'a'))
                                             (CanUnify (toTerm $ Var "x") (toTerm 'b'))
                            , expectOrRedo 2 (CanUnify (toTerm $ Var "x") (toTerm 'a'))
                                             (CanUnify (toTerm $ Var "x") (toTerm 'b'))
                            , expectCanUnifyCall 3 (Var "x") 'b'
                            , expectCanUnifyExit 3 'b'
                            , expectOrExit 2 (CanUnify (toTerm $ Var "x") (toTerm 'a'))
                                             (CanUnify (toTerm 'b') (toTerm 'b'))
                            , expectAlternativesExit 1 (Var "x" :: Var Char)
                                                       (Or (CanUnify (toTerm $ Var "x") (toTerm 'a'))
                                                           (CanUnify (toTerm $ Var "x") (toTerm 'b')))
                                                       ['a', 'b']
                            ]
    let alternativesFailInnerGoal = Alternatives (toTerm (Var "x" :: Var Char))
                                                 Bottom
                                                 (toTerm $ Var "xs")
    let alternativesFailInnerTrace = [ expectAlternativesCall 1 (Var "x" :: Var Char)
                                                                Bottom
                                                                (Var "xs")
                                     ] ++
                                       expectBottom 2 ++
                                     [ expectAlternativesExit 1 (Var "x" :: Var Char) Bottom Nil
                                     ]
    let alternativesFailGoal = Alternatives (toTerm (Var "x" :: Var Char)) Top Nil
    let alternativesFailTrace = [ expectAlternativesCall 1 (Var "x" :: Var Char) Top Nil
                                ] ++
                                  expectTop 2 ++
                                [ expectAlternativesFail 1 (Var "x" :: Var Char) Top Nil
                                ]
    let run g t c = runTest g (map (const c) [1..length t]) t

    it "should prompt after every step of computation" $ do
      let go g t = run g t "step"
      go deepGoal deepTrace
      go wideGoal wideTrace
      go backtrackingGoal backtrackingTrace
      go canUnifyGoal canUnifyTrace
      go canUnifyFailGoal canUnifyFailTrace
      go identicalGoal identicalTrace
      go identicalFailGoal identicalFailTrace
      go equalGoal equalTrace
      go equalFailGoal equalFailTrace
      go lessThanGoal lessThanTrace
      go lessThanFailGoal lessThanFailTrace
      go notGoal notTrace
      go notFailGoal notFailTrace
      go andGoal andTrace
      go andFailLeftGoal andFailLeftTrace
      go andFailRightGoal andFailRightTrace
      go orLeftGoal orLeftTrace
      go orRightGoal orRightTrace
      go orFailGoal orFailTrace
      go Top (expectTop 1)
      go Bottom (expectBottom 1)
      go alternativesGoal alternativesTrace
      go alternativesFailInnerGoal alternativesFailInnerTrace
      go alternativesFailGoal alternativesFailTrace
    it "should have a one-character alias" $ do
      let go g t = run g t "s"
      go deepGoal deepTrace
      go wideGoal wideTrace

  describe "the next command" $ do
    it "should skip to the next event at the current depth" $ do
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep)
        ["next", "next"]
        [ expectCall 1 "deep" (Var "x" :: Var Char)
        , expectExit 1 "deep" 'a'
        ]
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["next", "next"]
        [ expectCall 1 "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
        , expectExit 1 "wide" ('a', 'b', 'c')
        ]
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["step", "next", "next", "next", "next", "next", "next", "next"]
        [ expectCall 1 "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
        , expectCall 2 "foo" (Var "x" :: Var Char)
        , expectExit 2 "foo" 'a'
        , expectCall 2 "bar" (Var "y" :: Var Char)
        , expectExit 2 "bar" 'b'
        , expectCall 2 "baz" (Var "z" :: Var Char)
        , expectExit 2 "baz" 'c'
        , expectExit 1 "wide" ('a', 'b', 'c')
        ]
    it "if no more events at the current depth, it should stop at the next decrease in depth" $
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep)
        ["step", "next", "next", "next"]
        [ expectCall 1 "deep" (Var "x" :: Var Char)
        , expectCall 2 "foo" (Var "x" :: Var Char)
        , expectExit 2 "foo" 'a'
        , expectExit 1 "deep" 'a'
        ]
    it "should have a one-character alias" $
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep)
        ["n", "n"]
        [ expectCall 1 "deep" (Var "x" :: Var Char)
        , expectExit 1 "deep" 'a'
        ]

  describe "the finish command" $ do
    it "should skip to the next decrease in depth" $ do
      runTest (PredGoal (predicate "wide"
                (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["step", "finish", "step"]
        [ expectCall 1 "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
        , expectCall 2 "foo" (Var "x" :: Var Char)
        , expectExit 1 "wide" ('a', 'b', 'c')
        ]
      runTest (PredGoal (predicate "foo" (Var "x" :: Var Char)) backtracking)
        ["step", "finish", "finish"]
        [ expectCall 1 "foo" (Var "x" :: Var Char)
        , expectCall 2 "bar" (Var "x" :: Var Char)
        , expectFail 1 "foo" (Var "x" :: Var Char)
        ]
    it "should have a one-character alias" $
        runTest (PredGoal (predicate "wide"
                  (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)) wide)
        ["s", "f", "s"]
        [ expectCall 1 "wide" (Var "x" :: Var Char, Var "y" :: Var Char, Var "z" :: Var Char)
        , expectCall 2 "foo" (Var "x" :: Var Char)
        , expectExit 1 "wide" ('a', 'b', 'c')
        ]

  describe "the help command" $
    it "should print a usage message" $ do
      let run comm = runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep)
                      [comm, "f"]
                      [ expectCall 1 "deep" (Var "x" :: Var Char)
                      , debugHelp
                      ]
      run "?"
      run "h"
      run "help"

  describe "a blank command" $
    it "should repeat the previous command" $
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep)
        ["n", ""]
        [ expectCall 1 "deep" (Var "x" :: Var Char)
        , expectExit 1 "deep" 'a'
        ]

  describe "an unknown command" $
    it "should trigger a retry prompt" $
      runTest (PredGoal (predicate "deep" (Var "x" :: Var Char)) deep)
        ["bogus", "finish"]
        [ expectCall 1 "deep" (Var "x" :: Var Char)
        , "Unknown command \"bogus\". Try \"?\" for help."
        ]

  describe "an uninstantiated variables error" $
    it "should print the goal stack" $ do
      let goal = PredGoal (predicate "foo" (Var "x" :: Var Char))
                          [HornClause (predicate "foo" (Var "x" :: Var Char))
                                      (Equal (toTerm 'a') (toTerm (Var "x")))]
      let msg = "Variables are not sufficiently instantiated.\n" ++
                "Goal stack:\n" ++
                "(1) " ++ show (PredGoal (predicate "foo" (Var "x" :: Var Char)) []) ++ "\n" ++
                "(2) " ++ show (Equal (toTerm 'a') (toTerm (Var "x")))
      assertError msg $ runTest goal ["n", "n"] []
