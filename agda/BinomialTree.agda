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

  -- 1. Binomial trees are built from binomial heap
  --    https://en.wikipedia.org/wiki/Binomial_heap

  module Container where

    enum : ℕ → (ℕ → Set) → Set
    enum zero P = ⊤
    enum (suc n) P = enum n P × P n

    data Tree (A : Set) : ℕ → Set where
      node : ∀ {n} → A → enum n (Tree A) → Tree A n

    toVec : ∀ {A k} → Tree A k → Vec A (2 ^ k)
    toVecs : ∀ {A n} → A → enum n (Tree A) → Vec A (2 ^ n)

    toVec (node a ts) = toVecs a ts

    toVecs {n = zero} a tt = [ a ]
    toVecs {n = suc n} a (es , t) = toVecs a es ++ toVec t ++ []

    fromVec : ∀ {A} k → Vec A (2 ^ k) → Tree A k
    fromVecs : ∀ {A} k → Vec A (2 ^ k) → A × enum k (Tree A)

    fromVec zero (a ∷ []) = node a tt
    fromVec (suc k) vs with splitAt (2 ^ k) vs
    ... | (ls , rs , _) with splitAt (2 ^ k) rs
    ... | (rs , _ , _) with fromVecs k ls 
    ... | (a , t) = node a (t , fromVec k rs)

    fromVecs zero (a ∷ []) = a , tt
    fromVecs (suc k) vs with splitAt (2 ^ k) vs
    ... | (ls , rs , _) with splitAt (2 ^ k) rs
    ... | (rs , _ , _) with fromVecs k ls 
    ... | (a , t) = a , t , fromVec k rs

    iso-to-from : ∀ {A k} (t : Tree A k) → fromVec k (toVec t) ≡ t
    iso-to-from = {!TO BE DONE!}

    iso-from-to : ∀ {A} k (vs : Vec A (2 ^ k)) → toVec (fromVec k vs) ≡ vs
    iso-from-to = {!TO BE DONE!}

  -- 2. Composing `Datastructure` with `Container` to obtain the desired datatype

  open import Structure.Bin

  binomialTree : Set → Set
  binomialTree A = DBin Container.Tree
                        Container.toVec Container.fromVec
                        Container.iso-to-from Container.iso-from-to A

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
