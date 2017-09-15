module PseudoPerfect where

import Control.Hspl
import Data.Numbers.Primes

maxCandidatePrime :: Integer
maxCandidatePrime = 101

isComposite :: Predicate Integer
isComposite = predicate "isComposite" $
  match(integer "x") |- go? (v"x", 2 :: Integer)
  where go :: Predicate (Integer, Integer)
        go = predicate "isComposite.go" $ do
          match(v"x", v"y") |- do
            integer "x" |>=| v"y" |*| v"y"
            v"x" |%| v"y" |==| (0 :: Integer)
          match(v"x", v"y") |- do
            integer "y" |<| v"x"
            go? (v"x", v"y" |+| (1 :: Integer))

selectPrime :: Predicate ([Integer], Integer)
selectPrime = predicate "selectPrime" $ do
  match(v"x" <:> __, v"x") |- do
    v"x" |>| (1 :: Integer)
    lnot $ isComposite? v"x"
  match(__ <:> v"xs", v"y") |-
    selectPrime? (v"xs", v"y")

power :: Predicate (Integer, Integer, Integer)
power = predicate' [SemiDet] "power" $ do
  match(__, 0 :: Integer, 1 :: Integer)
  match(v"b", v"p", v"r") |- do
    v"p1" |==| v"p" |-| (1 :: Integer)
    power? (v"b", v"p1", v"r1")
    integer "r" |==| v"r1" |*| v"b"

-- | Compute 2^(p-1)(2^p - 1)
pseudoPerfect :: Predicate (Integer, Integer)
pseudoPerfect = predicate "pseudoPerfect" $
  match(v"p", v"r") |- do
    power?(2 :: Integer, v"p", v"2^p")
    v"r1" |==| v"2^p" |-| (1 :: Integer)
    power?(2 :: Integer, v"p" |-| (1 :: Integer), v"r2")
    integer "r" |==| v"r1" |*| v"r2"

selectPerfect :: Predicate ([Integer], Integer)
selectPerfect = predicate "selectPerfect" $ do
  match(v"p" <:> __, v"r") |- pseudoPerfect? (v"p", v"r")
  match(__ <:> v"ps", v"r") |- selectPerfect? (v"ps", v"r")

perfect :: Predicate Integer
perfect = predicate "perfect" $
  match(v"c") |- do
    findAll (integer "p") (selectPrime?([0..maxCandidatePrime], v"p")) (v"ps")
    selectPerfect?(v"ps", v"c")

expected :: [Integer]
expected = [2^(p-1) * (2^p - 1) | p <- [0..maxCandidatePrime], isPrime p]
