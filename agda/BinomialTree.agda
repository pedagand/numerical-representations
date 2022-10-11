{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.Vec hiding (insert ; concat)

open import Relation.Binary.Core
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.HeterogeneousEquality hiding ([_])

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

module BinomialTree where

  -- Composing 01-binary structure with binomial heaps

  open import Structure.Bin
  open import Container.BinomialHeap
  
  binomialTree : Set → Set
  binomialTree A = DBin Container.BinomialHeap.Tree
                        Container.BinomialHeap.toVec Container.BinomialHeap.fromVec
                        Container.BinomialHeap.iso-to-from Container.BinomialHeap.iso-from-to A

  -- TODO: implement all the operations on the datastructure:
  --   cf. "Numerical representation as higher-order nested datatypes", Fig. 5, p.21 for the interface
  --   cf. Okasaki, [Hinze 1998](https://dl.acm.org/doi/10.1017/S0956796899003317)

  module API (A : Set)
             (_≈_ : Rel A Agda.Primitive.lzero)
             (_≤_ : Rel A Agda.Primitive.lzero)
             (_ : IsTotalOrder _≈_ _≤_)
    where

    empty : binomialTree A
    empty = {!!}

    splitMin : binomialTree A → A × binomialTree A
    splitMin = {!!}

    splitMax : binomialTree A → binomialTree A × A
    splitMax = {!!}

    member : A → binomialTree A → Bool
    member = {!!}

    insert : A → binomialTree A → binomialTree A
    insert = {!!}

    delete : A → binomialTree A → binomialTree A
    delete = {!!}

    concat : binomialTree A → binomialTree A → binomialTree A
    concat = {!!}

    partition : A → binomialTree A → binomialTree A × binomialTree A
    partition = {!!}

    merge : binomialTree A → binomialTree A → binomialTree A
    merge = {!!}
