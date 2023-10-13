{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat renaming (suc to sucℕ)
open import Relation.Binary.PropositionalEquality

open import Numerical.Nat.Properties

module Numerical.SkewBinary.Sparse where

data Skew : Set where
  ϵ  : Skew
  _I[_] : Skew → ℕ → Skew
  _T[_] : Skew → ℕ → Skew

Skew⇒Nat-g : Skew → ℕ → ℕ
Skew⇒Nat-g ϵ k = 0
Skew⇒Nat-g (bs I[ c ]) k =
  {- 1 * -} 2^[ k + c +1]-1
  + Skew⇒Nat-g bs (1 + k + c)
Skew⇒Nat-g (bs T[ c ]) k =
  {- 2 * 2^[ k +1]-1 = -}
     2^[ k + c +1]-1 + 2^[ k + c +1]-1
  + Skew⇒Nat-g bs (1 + k + c)

Skew⇒Nat : Skew → ℕ
Skew⇒Nat bs = Skew⇒Nat-g bs 0

-- XXX: this cannot be implemented in constant-time because we have
-- carries that could propgate (case `bs T T`) which makes this
-- representation useless for the intended data-structure
incr : Skew → Skew
incr ϵ = ϵ I[ 0 ]
incr (bs I[ zero ]) = bs T[ zero ]
incr (bs I[ sucℕ x ]) = bs I[ x ] I[ 0 ]
incr (ϵ T[ x ]) = ϵ I[ 1 + x ]
incr ((bs I[ zero ]) T[ x ]) = bs T[ 1 + x ]
incr ((bs I[ sucℕ x₁ ]) T[ x ]) = bs I[ x₁ ] I[ 1 + x ]
incr ((bs T[ x₁ ]) T[ x ]) = {!!}
