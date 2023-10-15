{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Product
open import Data.Nat
open import Data.Maybe

module BinaryRandomAccessList where

{-

From

  "Numerical representation as higher-order nested datatypes", Hinze

in Haskell with nested types:

 > data Fork t a = Fork (t a) (t a)
 >
 > data RandomAccessList bush a =
 >  | Nil
 >  | Zero (RandomAccessList (Fork bush) a)
 >  | One (bush a) (RandomAccessList (Fork bush) a)

 > data Id a = Id a
 > data IxSequence a = RandomAccessList Id a

-}

open import Container.Binary.LeafBinaryTree
open import Structure.Binary.Dense Tree toVec fromVec iso-to-from iso-from-to

RAL : Set → Set
RAL A = DBin0 A

-- TODO: implement all the operations on the datastructure:
--   cf. "Numerical representation as higher-order nested datatypes", Fig. 3, p.13 for the interface
--   cf. Okasaki, Sec. 9.2.1 and 10.1.2 for the implementation

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
