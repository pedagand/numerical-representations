open import Data.Nat

-- Binary numbers are the "numerical representation" underlying
-- various data-structures

module Numerical.Bin where

  data Bin : Set where
    ϵ  : Bin
    _O : Bin → Bin
    _I : Bin → Bin

  Bin⇒Nat-g : Bin → ℕ → ℕ
  Bin⇒Nat-g ϵ k = 0
  Bin⇒Nat-g (bs O) k = {- 0 * 2 ^ k + -} Bin⇒Nat-g bs (1 + k)
  Bin⇒Nat-g (bs I) k = {- 1 * -} 2 ^ k + Bin⇒Nat-g bs (1 + k)

  Bin⇒Nat : Bin → ℕ
  Bin⇒Nat b = Bin⇒Nat-g b 0
