module SolverTest where

import Testing
import Control.Hspl.Internal.Ast
import Control.Hspl.Internal.Solver
import Control.Hspl.Internal.Unification
import Data.Monoid

-- x is a member of x:xs
member1 = HornClause (predicate "member" ( Var "x" :: Var Int
                                         , List (toTerm (Var "x" :: Var Int))
                                                (toTerm (Var "_" :: Var [Int]))))
                     []
-- x is a member of _:xs if x is a member of xs
member2 = HornClause (predicate "member" ( Var "x" :: Var Int
                                         , List (toTerm (Var "_" :: Var Int))
                                                (toTerm (Var "xs" :: Var [Int]))))
                     [predicate "member" (Var "x" :: Var Int, Var "xs" :: Var [Int])]
memberProgram = addClauses [member1, member2] emptyProgram

-- All humans are mortal
mortal = HornClause (predicate "mortal" (Var "x" :: Var String))
                    [predicate "human" (Var "x" :: Var String)]
-- Hypatia is human
human1 = HornClause (predicate "human" "hypatia") []
-- So is Fred
human2 = HornClause (predicate "human" "fred") []

syllogism = addClauses [mortal, human1, human2] emptyProgram

example0 = addClause (HornClause (predicate "foo" ('a', 'b')) []) emptyProgram

example1 = addClauses [ HornClause ( predicate "foo" (Var "x" :: Var Char, Var "y" :: Var Char))
                                   [ predicate "bar" (Var "x" :: Var Char)
                                   , predicate "baz" (Var "y" :: Var Char)
                                   ]
                      , HornClause ( predicate "bar" 'a' ) []
                      , HornClause ( predicate "baz" 'b' ) []
                      ] emptyProgram

noUnification = addClauses [HornClause (predicate "foo" (Var "x" :: Var Char)) []] emptyProgram

partialUnification = addClauses [HornClause (predicate "foo" (Var "x" :: Var Char, 'b')) []] emptyProgram

test = describeModule "Control.Hspl.Internal.Solver" $ do
  describe "a proof search" $ do
    it "should traverse every branch of the proof" $ do
      let p = predicate "p" ()
      let q = predicate "q" ()
      let r = predicate "r" ()
      let wideProof = (Proof p [Axiom p, Axiom  q, Axiom r], mempty)
      let deepProof = (Proof p [Proof q [Axiom r]], mempty)
      searchProof (Axiom p, mempty) p `shouldBe` [p]
      searchProof wideProof p `shouldBe` [p, p]
      searchProof wideProof q `shouldBe` [q]
      searchProof wideProof r `shouldBe` [r]
      searchProof deepProof p `shouldBe` [p]
      searchProof deepProof q `shouldBe` [q]
      searchProof deepProof r `shouldBe` [r]
    it "should find subgoals which unify with the query" $
      searchProof (Proof (predicate "p" (Var "x" :: Var Char, 'b'))
                         [Axiom $ predicate "p" ('a', Var "x" :: Var Char)], mempty)
                  (predicate "p" (Var "x" :: Var Char, Var "y" :: Var Char)) `shouldBePermutationOf`
        [predicate "p" (Var "x" :: Var Char, 'b'), predicate "p" ('a', Var "x" :: Var Char)]
  describe "the \"get solutions\" feature" $ do
    it "should return the theorem at the root of a proof tree" $ do
      getSolution (Proof (predicate "p" ()) [ Proof (predicate "q" () ) [Axiom $ predicate "r" ()]
                                            , Axiom (predicate "s" ())
                                            ], mempty) `shouldBe`
        predicate "p" ()
      getSolution (Axiom $ predicate "p" (), mempty) `shouldBe` predicate "p" ()
    it "should get all solutions from a forest of proof tress" $
      getAllSolutions [ (Axiom $ predicate "p" (), mempty)
                      , (Axiom $ predicate "q" (), mempty)] `shouldBe`
        [predicate "p" (), predicate "q" ()]
  describe "the \"get unifiers\" feature" $ do
    it "should return the unifier from a solution" $ do
      let u = toTerm 'a' // Var "x" <> toTerm True // Var "y"
      getUnifier (Axiom $ predicate "foo" (), u) `shouldBe` u
    it "should return all unifiers from a solution forest" $ do
      let u1 = toTerm 'a' // Var "x"
      let u2 = toTerm True // Var "y"
      getAllUnifiers [(Axiom $ predicate "foo" (), u1), (Axiom $ predicate "bar" (), u2)] `shouldBe`
        [u1, u2]
  describe "the HSPL solver" $ do
    it "should return all proofs of the query" $ do
      let (proofs, _) = unzip $ runHspl syllogism (predicate "mortal" "hypatia")
      proofs `shouldBe` [Proof (predicate "mortal" "hypatia") [Axiom (predicate "human" "hypatia")]]
      let (proofs2, _) = unzip $ runHspl syllogism (predicate "mortal" (Var "x" :: Var String))
      proofs2 `shouldBePermutationOf`
        [ Proof (predicate "mortal" "hypatia") [Axiom (predicate "human" "hypatia")]
        , Proof (predicate "mortal" "fred") [Axiom (predicate "human" "fred")]
        ]
    it "should return the requested number of proofs" $ do
      let (proofs, _) = unzip $ runHsplN 1 syllogism $ predicate "mortal" (Var "x" :: Var String)
      proofs `shouldBeSubsetOf`
        [ Proof (predicate "mortal" "hypatia") [Axiom (predicate "human" "hypatia")]
        , Proof (predicate "mortal" "fred") [Axiom (predicate "human" "fred")]
        ]
      length proofs `shouldBe` 1
    it "should handle a proof with multiple subgoals" $ do
      let (proofs, _) = unzip $ runHspl example1 (predicate "foo" (Var "x" :: Var Char, Var "y" :: Var Char))
      proofs `shouldBe` [Proof ( predicate "foo" ('a', 'b'))
                               [ Axiom $ predicate "bar" 'a'
                               , Axiom $ predicate "baz" 'b']
                        ]
    it "should indicate when variables have been substituted" $ do
      let (_, us) = unzip $ runHspl memberProgram (predicate "member" (Var "x" :: Var Int, [1 :: Int]))
      length us `shouldBe` 1
      head us `shouldSatisfy` (((1 :: Int) // Var "x") `isSubunifierOf`)
    it "should return a unifier for each solution" $ do
      let (_, us) = unzip $ runHspl syllogism (predicate "mortal" (Var "x" :: Var String))
      length us `shouldBe` 2
      if head us `isSubunifierOf` ("hypatia" // Var "x")
        then last us `shouldSatisfy` (("fred" // Var "x") `isSubunifierOf`)
        else do head us `shouldSatisfy` (("fred" // Var "x") `isSubunifierOf`)
                last us `shouldSatisfy` (("hypatia" // Var "x") `isSubunifierOf`)
    it "should handle multiple variables" $ do
      let (_, us) = unzip $ runHspl example0 (predicate "foo" (Var "x" :: Var Char, Var "y" :: Var Char))
      length us `shouldBe` 1
      head us `shouldSatisfy` (('a' // Var "x" <> 'b' // Var "y") `isSubunifierOf`)
