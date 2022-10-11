{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Maybe
open import Data.Vec

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.HeterogeneousEquality hiding ([_])

open import Structure.Bin
open import Container.LeafBinaryTree

{-

From

  "Numerical representation as higher-order nested datatypes", Hinze

in Haskell with nested types:

 > data Fork t a = Fork (t a) (t a)
 >
 > data RandomAccessList bush a =
 >  | Nil
 >  | One (bush a) (RandomAccessList (Fork bush) a)
 >  | Two (Fork bush a) (RandomAccessList (Fork bush) a)

 > data Id a = Id a
 > data IxSequence a = RandomAccessList Id a

-}

module OneTwoRandomAccessList where

  -- Composing 12-binary structure with leaf binary tree to obtain the
  -- desired datatype.

  open import Structure.OneTwo
  open import Container.LeafBinaryTree

  RAL : Set → Set
  RAL A = DOneTwo Container.LeafBinaryTree.Tree
                  Container.LeafBinaryTree.toVec Container.LeafBinaryTree.fromVec
                  Container.LeafBinaryTree.iso-to-from Container.LeafBinaryTree.iso-from-to A


  -- TODO: implement all the operations on the datastructure:
  --   cf. "Numerical representation as higher-order nested datatypes", Fig. 3, p.13 
  -- for the interface and implementation

  empty : ∀ {A} → RAL A
  empty = {!!}

  cons : ∀ {A} → A → RAL A → RAL A
  cons = {!!}

  front : ∀ {A} → RAL A → A × RAL A
  front = {!!}

  snoc : ∀ {A} → RAL A → A → RAL A
  snoc = {!!}

  rear : ∀ {A} → RAL A → A × RAL A
  rear = {!!}

  access : ∀ {A} → RAL A → ℕ → Maybe A
  access = {!!}

  update : ∀ {A} → RAL A → ℕ → A → RAL A
  update = {!!}
