{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Nat
open import Data.Vec
open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.HeterogeneousEquality hiding ([_])

-- [Binomial heap](https://en.wikipedia.org/wiki/Binomial_heap)
-- Okasaki, Definition 9.2, p.118

module Container.Binary.BinomialHeap where

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
