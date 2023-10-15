{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.Maybe

open import Relation.Binary

{-

From

  "Numerical representation as higher-order nested datatypes", Hinze

in Haskell with nested types

 > data Snoc subtrees a = Snoc (subtrees a) (Node subtrees a)
 >
 > data Node subtrees a = Node a (subtrees a)
 >
 > data BinomialQueue subtrees a
 >  = Nil
 >  | Zero (BinomialQueue (Snoc subtrees) a)
 >  | One (Node subtree a) (BinomialQueue (Snoc subtrees) a)
 >
 > data Id a = Id a
 > data Queue a = BinomialQueue Id a

-}

module BinomialTree (A : Set)
                    (_≈_ : Rel A Agda.Primitive.lzero)
                    (_≤_ : Rel A Agda.Primitive.lzero)
                    (_ : IsTotalOrder _≈_ _≤_) where

open import Container.Binary.BinomialHeap
open import Structure.Binary.Dense Tree toVec fromVec iso-to-from iso-from-to

BinomialTree : Set → Set
BinomialTree A = DBin0 A

-- TODO: implement all the operations on the datastructure:
--   cf. "Numerical representation as higher-order nested datatypes", Fig. 5, p.21 for the interface
--   cf. Okasaki, [Hinze 1998](https://dl.acm.org/doi/10.1017/S0956796899003317)

empty : BinomialTree A
empty = {!!}

splitMin : BinomialTree A → A × BinomialTree A
splitMin = {!!}

splitMax : BinomialTree A → BinomialTree A × A
splitMax = {!!}

member : A → BinomialTree A → Bool
member = {!!}

insert : A → BinomialTree A → BinomialTree A
insert = {!!}

delete : A → BinomialTree A → BinomialTree A
delete = {!!}

concat : BinomialTree A → BinomialTree A → BinomialTree A
concat = {!!}

partition : A → BinomialTree A → BinomialTree A × BinomialTree A
partition = {!!}

merge : BinomialTree A → BinomialTree A → BinomialTree A
merge = {!!}
