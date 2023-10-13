{-# OPTIONS --allow-unsolved-metas #-}

module Numerical.Nat.Properties where

open import Data.Nat renaming (suc to sucℕ)
open import Relation.Binary.PropositionalEquality

rewrite-+0 : ∀ n → n + 0 ≡ n
rewrite-+0 zero = refl
rewrite-+0 (sucℕ n) rewrite rewrite-+0 n = refl

rewrite-+S : ∀ n m → n + sucℕ m ≡ sucℕ (n + m)
rewrite-+S zero m = refl
rewrite-+S (sucℕ n) m rewrite rewrite-+S n m = refl

rewrite-+-comm : ∀ m n o → m + (n + o) ≡ m + n + o
rewrite-+-comm zero n o = refl
rewrite-+-comm (sucℕ m) n o rewrite rewrite-+-comm m n o = refl


2^[_+1]-1 : ℕ → ℕ
2^[ zero +1]-1 = 1
2^[ sucℕ k +1]-1 = sucℕ (2^[ k +1]-1 + 2^[ k +1]-1)
  -- where n = 2^[ k +1]-1

pf-2^−1-spec : ∀ k → 2^[ k +1]-1 ≡ pred (2 ^ (k + 1))
pf-2^−1-spec zero = refl
pf-2^−1-spec (sucℕ k) rewrite pf-2^−1-spec k = {!TRUE!}

pf-carry : ∀ c → sucℕ (2^[ c +1]-1 + 2^[ c +1]-1) ≡ 2^[ sucℕ c +1]-1
pf-carry c = refl
