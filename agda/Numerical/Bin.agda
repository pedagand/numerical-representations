open import Data.Nat

-- Binary numbers are the "numerical representation" underlying
-- various data-structures

module Numerical.Bin where

data Bin : Set where
  ϵ  : Bin
  _O : Bin → Bin
  _I : Bin → Bin

incr : Bin → Bin
incr ϵ = ϵ I
incr (b O) = b I
incr (b I) = incr b O

Bin⇒ℕ-g : Bin → ℕ → ℕ
Bin⇒ℕ-g ϵ k = 0
Bin⇒ℕ-g (bs O) k = {- 0 * 2 ^ k + -} Bin⇒ℕ-g bs (suc k)
Bin⇒ℕ-g (bs I) k = {- 1 * -} 2 ^ k + Bin⇒ℕ-g bs (suc k)

Bin⇒ℕ : Bin → ℕ
Bin⇒ℕ b = Bin⇒ℕ-g b 0

ℕ⇒Bin : ℕ → Bin
ℕ⇒Bin zero = ϵ
ℕ⇒Bin (suc n) = incr (ℕ⇒Bin n)
