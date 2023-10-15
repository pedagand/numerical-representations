{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Fin hiding (_+_) renaming (suc to sucF)
open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import Numerical.Nat.Properties

import Numerical.Generic.RunLength

module Numerical.SkewBinary.Sparse where


base : ℕ → ℕ
base k = 2^[ k +1]-1

mode : Set
mode = ⊤

op : mode → ℕ
op m = 2

ar : ∀ {m} → Fin (op m) → ℕ
ar zero = 0
ar (sucF zero) = 1

nx : ∀ {m} → Fin (op m) → mode
nx _ = tt

module SkewBinary = Numerical.Generic.RunLength base mode op ar nx

open SkewBinary

Skew = Num tt

Skew⇒Nat : Skew → ℕ
Skew⇒Nat = SkewBinary.toℕ

Skew⇒Nat-help = toℕ-help

pattern _I[_] bs c = C zero c bs
pattern _T[_] bs c = C (sucF zero) c bs

_ : Skew⇒Nat ϵ ≡ 0
_ = refl

_ : Skew⇒Nat (ϵ I[ 0 ]) ≡ 1
_ = refl

_ : Skew⇒Nat (ϵ T[ 0 ]) ≡ 2
_ = refl

_ : Skew⇒Nat (ϵ I[ 1 ]) ≡ 3
_ = refl

_ : Skew⇒Nat (ϵ I[ 0 ] I[ 0 ]) ≡ 4
_ = refl

_ : Skew⇒Nat (ϵ I[ 0 ] T[ 0 ]) ≡ 5
_ = refl

_ : Skew⇒Nat (ϵ T[ 1 ]) ≡ 6
_ = refl

_ : Skew⇒Nat (ϵ I[ 2 ]) ≡ 7
_ = refl

_ : Skew⇒Nat (ϵ I[ 3 ]) ≡ 15
_ = refl

_ : Skew⇒Nat (ϵ I[ 1 ] T[ 2 ]) ≡ 45
_ = refl

-- Isomorphism with direct representation:

data Skew-View : Skew → Set where
  is-ϵ  : Skew-View ϵ
  is-_I[_] : ∀ {bs} → Skew-View bs → (c : ℕ) → Skew-View (bs I[ c ])
  is-_T[_] : ∀ {bs} → Skew-View bs → (c : ℕ) → Skew-View (bs T[ c ])

Skew-view : ∀ bs → Skew-View bs
Skew-view ϵ = is-ϵ
Skew-view (bs I[ c ]) = is- Skew-view bs I[ c ]
Skew-view (bs T[ c ]) = is- Skew-view bs T[ c ]

-- Operations:

-- Remark: this cannot be implemented in constant-time because we have
-- carries that could propgate (case `bs T T`) which makes this
-- representation useless for the intended data-structure

incr : Skew → Skew
incr ϵ = ϵ I[ 0 ]
incr (bs I[ zero ]) = bs T[ zero ]
incr (bs I[ suc x ]) = bs I[ x ] I[ 0 ]
incr (ϵ T[ x ]) = ϵ I[ 1 + x ]
incr ((bs I[ zero ]) T[ x ]) = bs T[ 1 + x ]
incr ((bs I[ suc x₁ ]) T[ x ]) = bs I[ x₁ ] I[ 1 + x ]
incr ((bs T[ x₁ ]) T[ x ]) = {!!}
