open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Maybe
open import Data.Vec

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.HeterogeneousEquality hiding ([_])

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

  -- 1. Random-access lists are built from leaf binary tree.

  module Container where

    data Tree (A : Set) : ℕ → Set where
      Leaf : A → Tree A 0
      Node : ∀ {n} → Tree A n → Tree A n → Tree A (suc n)

    toVec : ∀ {A k} → Tree A k → Vec A (2 ^ k)
    toVec (Leaf x) = [ x ]
    toVec (Node t₁ t₂) = toVec t₁ ++ toVec t₂ ++ []

    fromVec : ∀ {A} k → Vec A (2 ^ k) → Tree A k
    fromVec zero (a ∷ []) = Leaf a
    fromVec (suc k) vs with splitAt (2 ^ k) vs
    ... | (ls , rs , _ ) with splitAt (2 ^ k) rs
    ... | (rs , _ , _) = Node (fromVec k ls) (fromVec k rs)

    iso-to-from : ∀ {A k} (t : Tree A k) → fromVec k (toVec t) ≡ t
    iso-to-from = {!TO BE DONE!}

    iso-from-to : ∀ {A} k (vs : Vec A (2 ^ k)) → toVec (fromVec k vs) ≡ vs
    iso-from-to = {!TO BE DONE!}


  -- 2. Composing `Datastructure` with `Container` to obtain the desired datatype

  open import Structure.OneTwo

  RAL : Set → Set
  RAL A = DOneTwo Container.Tree
                  Container.toVec Container.fromVec
                  Container.iso-to-from Container.iso-from-to A


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
