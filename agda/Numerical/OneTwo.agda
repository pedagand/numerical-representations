open import Data.Nat

module Numerical.OneTwo where

  data OneTwo : Set where
    ϵ  : OneTwo
    _I : OneTwo → OneTwo
    _T : OneTwo → OneTwo

  OneTwo⇒Nat-g : OneTwo → ℕ → ℕ
  OneTwo⇒Nat-g ϵ k = 0
  OneTwo⇒Nat-g (bs I) k = {- 1 * -} 2 ^ k + OneTwo⇒Nat-g bs (1 + k)
  OneTwo⇒Nat-g (bs T) k = {- 2 * 2 ^ k = -} 2 ^ k + 2 ^ k + OneTwo⇒Nat-g bs (1 + k)

  OneTwo⇒Nat : OneTwo → ℕ
  OneTwo⇒Nat b = OneTwo⇒Nat-g b 0
