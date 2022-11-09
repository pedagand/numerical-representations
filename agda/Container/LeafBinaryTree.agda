{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Vec
open import Data.Product
open import Data.Fin using (Fin)
open import Function

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.HeterogeneousEquality hiding ([_])

module Container.LeafBinaryTree where

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

  -- To be improved, we are working with binary trees after all
  -- It is sad to transform to vectors to lookup, but it's late
  -- and I don't want to handle decidability cases with 2^k-1
  lookup-tree : ∀ {A k} → Tree A k → Fin (2 ^ k) → A
  lookup-tree = lookup ∘ toVec

  update-tree : ∀ {A k} → Fin (2 ^ k) → A → Tree A k → Tree A k
  update-tree i a = fromVec _ ∘ (updateAt i (const a)) ∘ toVec

  iso-to-from : ∀ {A k} (t : Tree A k) → fromVec k (toVec t) ≡ t
  iso-to-from = {!TO BE DONE!}

  iso-from-to : ∀ {A} k (vs : Vec A (2 ^ k)) → toVec (fromVec k vs) ≡ vs
  iso-from-to = {!TO BE DONE!}
