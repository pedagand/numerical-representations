{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Vec
open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.HeterogeneousEquality hiding ([_])

-- Okasaki, Definition 9.1, p.118

module Container.Binary.LeafBinaryTree where

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
