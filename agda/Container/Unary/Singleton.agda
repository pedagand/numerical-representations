{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Vec

module Container.Unary.Singleton where

Unary : (A : Set)(k : ℕ) → Set
Unary A k = A

toVec : ∀ {A k} → Unary A k → Vec A (1 ^ k)
toVec a = {!!}

fromVec : ∀ {A} k → Vec A (1 ^ k) → Unary A k
fromVec v = {!!}
