{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Vec
open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.HeterogeneousEquality hiding ([_])

-- Okasaki, Definition 9.1, p.118

module Container.SkewBinary.CompleteBinaryTree where

data Tree (A : Set) : ℕ → Set where
  Leaf : A → Tree A 0
  Node : ∀ {n} → Tree A n → A → Tree A n → Tree A (suc n)

toVec : ∀ {A k} → Tree A k → Vec A (pred (2 ^ (1 + k)))
toVec (Leaf a) = [ a ]
toVec (Node t₁ a t₂) with toVec t₁ | toVec t₂
... | vs₁ | vs₂ = {!!}

fromVec : ∀ {A} k → Vec A (pred (2 ^ (1 + k))) → Tree A k
fromVec k vs = {!!}

{-
iso-to-from : ∀ {A k} (t : Tree A k) → fromVec k (toVec t) ≡ t
iso-to-from = {!TO BE DONE!}

iso-from-to : ∀ {A} k (vs : Vec A (2 ^ k)) → toVec (fromVec k vs) ≡ vs
iso-from-to = {!TO BE DONE!}
-}
