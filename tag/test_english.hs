{-# OPTIONS -Wall -fno-warn-missing-signatures #-}
module Main (main) where

import Control.Monad (forM_)
import Tig5 (NonTerminal(..), mkTIG, mkTree, showTree, parse, footN, termTree, termTreeN, mkTreeN, ntN)
import qualified Data.Set as Set

-- ===================================================================================================
-- A very incomplete grammar for English
-- ===================================================================================================
_S = NonTerminal "S"
_NP = NonTerminal "NP"
_VP = NonTerminal "VP"
_V = NonTerminal "V"
_N = NonTerminal "N"
_D = NonTerminal "D"
_P = NonTerminal "P"
_PP = NonTerminal "PP"
_Adv = NonTerminal "Adv"
_Adj = NonTerminal "Adj"
_Conj = NonTerminal "Conj"

mkNoun = termTree _N
mkNP str = mkTree _NP [termTreeN _D str, ntN _N]
mkVP str = mkTree _VP [termTreeN _V str, ntN _NP]
mkAdjNoun str = mkTree _N [termTreeN _Adj str, footN _N]

g = mkTIG
    -- init_trees
      -- nouns
    [ mkNoun "apple"
    , mkNoun "banana"
    , mkNoun "boy"
    , mkNoun "telescope"
    , mkNoun "ideas"
    , mkNoun "glasses"

      -- _NP's
    , termTree _NP "john"
    , termTree _NP "mary"
    , termTree _NP "bill"

    , mkNP "some"
    , mkNP "a"
    , mkNP "an"
    , mkNP "the"

      -- some intransitive verbs
    , mkTree _VP [termTreeN _V "ran"]
    , mkTree _VP [termTreeN _V "sleep"]

      -- some transitive verbs
    , mkVP "kissed"
    , mkVP "hugged"
    , mkVP "ate"
    , mkVP "saw"

      -- _S itself is non lexicalized, but this is required to allow _VP-level adjunction
    , mkTree _S [ntN _NP, ntN _VP]
    ]
    -- aux_trees
      -- some adjectives
    [ mkAdjNoun "nice"
    , mkAdjNoun "little"
    , mkAdjNoun "tasty"
    , mkAdjNoun "colorless"
    , mkAdjNoun "green"

      -- some adverbs
    , mkTree _Adj [termTreeN _Adv "very", footN _Adj]
    , mkTree _VP [termTreeN _Adv "really", footN _VP]
    , mkTree _VP [footN _VP, termTreeN _Adv "quickly"]
    , mkTree _VP [footN _VP, termTreeN _Adv "furiously"]

      -- _PP's can adjoin both _N's and _VP's
    , mkTree _N [footN _N, mkTreeN _PP [termTreeN _P "with", ntN _NP]]
    , mkTree _VP [footN _VP, mkTreeN _PP [termTreeN _P "with", ntN _NP]]

      -- conjunction (at _V, _N, _NP and _VP levels)
    , mkTree _NP [footN _NP, termTreeN _Conj "and", ntN _NP]
    , mkTree _N [footN _N, termTreeN _Conj "and", ntN _N]
    , mkTree _VP [footN _VP, termTreeN _Conj "and", ntN _VP]
    , mkTree _V [ntN _V, termTreeN _Conj "and", footN _V]
    ]


-- ===================================================================================================
-- All sorts of sentences we can be derived from this grammar (the last two are ambiguous)
-- which we use to test the parser
-- ===================================================================================================
sentences =
    -- adjunction
  [ "john saw the boy"
  , "john saw the nice boy"
  , "john saw the nice little boy"
  , "john ate the very tasty apple"
  , "some colorless green ideas sleep furiously"

    -- conjunction
  , "john and mary ate the banana"
  , "john ate the banana and the apple"
  , "john ate the banana and apple"
  , "john ate the apple and saw the boy"
  , "john kissed and hugged mary"

    -- ambiguity
  , "john saw the nice boy with the telescope"
  , "john saw the boy with the glasses and the telescope"
  ]

main = forM_ sentences $ \text -> do
  putStrLn "==============================================================="
  putStrLn text
  putStrLn "==============================================================="
  let trees = parse g _S $ words text
  forM_ (zip [(1::Int)..] (Set.toList trees)) $ \(i, t) -> do
      putStrLn $ "(" ++ show i ++ ")"
      putStrLn $ showTree t
      putStrLn ""
