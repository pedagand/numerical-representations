open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (_+_) renaming (toℕ to Fin-toℕ)
open import Data.Vec renaming (map to map-Vec ; sum to sum-Vec)
open import Data.Product renaming (map to map×)
open import Data.Sum renaming (map to mapΣ)
open import Relation.Binary.PropositionalEquality

module Numerical.Generic.RunLength
      -- Choose a numerical base:
      (base : ℕ → ℕ)
      -- Choose a numerical repr:
      (mode : Set)
      (op : mode → ℕ)
      (ar : ∀ {m} → Fin (op m) → ℕ)
      (nx : ∀ {m} → Fin (op m) → mode)
    where

data Num : mode → Set where
  ϵ : ∀ {m} → Num m
  C : ∀ {m} → (d : Fin (op m))(c : ℕ) → Num (nx d) → Num m

toℕ-help : ∀ {m} → Num m → ℕ → ℕ
toℕ-help ϵ k = 0
toℕ-help (C d c n) k = (suc (ar d)) * base (k + c) + toℕ-help n (1 + k + c)

toℕ : ∀ {m} → Num m → ℕ
toℕ n = toℕ-help n 0
