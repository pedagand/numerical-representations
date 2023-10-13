{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Relation.Binary.PropositionalEquality

module Numerical.Binary.Sparse where

data Bin : Set where
  ϵ : Bin
  _I[_] : Bin → ℕ → Bin

Bin⇒Nat-g : Bin → ℕ → ℕ
Bin⇒Nat-g ϵ k = 0
Bin⇒Nat-g (bs I[ c ]) k = {- 1 * -} 2 ^ (1 + c + k) + Bin⇒Nat-g bs (1 + c + k)

Bin⇒Nat : Bin → ℕ
Bin⇒Nat b = Bin⇒Nat-g b 0

carry : Bin → Bin
carry = {!!}

borrow : Bin → Bin
borrow = {!!}

inc : Bin → Bin
inc = {!!}

dec : Bin → Bin
dec = {!!}

add : Bin → Bin → Bin
add = {!!}
