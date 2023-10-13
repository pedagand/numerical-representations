{-# OPTIONS --rewriting #-}

open import Data.Fin hiding (_+_ ; pred)
open import Data.Nat renaming (suc to sucℕ)
open import Relation.Binary.PropositionalEquality

open import Numerical.Nat.Properties

import Numerical.Generic.RunLength

{-# BUILTIN REWRITE _≡_ #-}

module Numerical.SkewBinary.SparseCanonical where

base : ℕ → ℕ
base k = 2^[ k +1]-1

data mode : Set where
  C I : mode

op : mode → ℕ
op m = sucℕ (op2 m)
  where op2 : mode → ℕ
        op2 C = 1
        op2 I = 0

ar : ∀ {m} → Fin (op m) → ℕ
ar zero = 0
ar {C} (suc zero) = 1

nx : ∀ {m} → Fin (op m) → mode
nx zero = I
nx {C} (suc zero) = I

module SkewBinary = Numerical.Generic.RunLength base mode op ar nx

open SkewBinary

Skew = Num
Skew⇒Nat : Skew C → ℕ
Skew⇒Nat = SkewBinary.toℕ

pattern _I[_] bs c = C zero c bs
pattern _T[_] bs c = C (suc zero) c bs


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

data Skew-View : ∀ {m} → Skew m → Set where
  is-ϵ : ∀ {m} → Skew-View {m} ϵ
  is-_I[_] : ∀ {m} {bs} (n : Skew-View bs) (c : ℕ) →
          Skew-View {m} (C zero c bs)
  is-_T[_] : ∀ {bs} (n : Skew-View bs) (c : ℕ) →
          Skew-View {C} (C (suc zero) c bs)

Skew-view : ∀ {m} → (bs : Skew m) → Skew-View bs
Skew-view ϵ = is-ϵ
Skew-view (bs I[ c ]) = is- Skew-view bs I[ c ]
Skew-view {C} (bs T[ c ]) = is- Skew-view bs T[ c ]

-- Operations:

incr : Skew C → Skew C
incr ϵ = ϵ I[ 0 ]
incr (bs I[ 0 ]) = bs T[ 0 ]
incr (bs I[ sucℕ c ]) = bs I[ c ] I[ 0 ]
incr (ϵ T[ c ]) = ϵ I[ sucℕ c ]
incr (bs I[ zero ] T[ c ]) = bs T[ sucℕ c ]
incr (bs I[ sucℕ c₁ ] T[ c ]) = bs I[ c₁ ] I[ sucℕ c ]

decr : Skew C → Skew C
decr ϵ = ϵ
decr (bs T[ zero ]) = bs I[ zero ]
decr (bs T[ sucℕ c ]) = bs I[ 0 ] T[ c ]
decr (ϵ I[ zero ]) = ϵ
decr (bs I[ c ] I[ zero ]) = bs I[ sucℕ c ]
decr (ϵ I[ sucℕ c ]) = ϵ T[ c ]
decr (bs I[ c₁ ] I[ sucℕ c ]) = bs I[ sucℕ c₁ ] T[ c ]

-- Correctness:

{-# REWRITE rewrite-+0 rewrite-+S rewrite-+-comm #-}

pf-incr : ∀ s → 1 + (Skew⇒Nat s) ≡ Skew⇒Nat (incr s)
pf-incr ϵ = refl
pf-incr (bs I[ zero ]) = refl
pf-incr (bs I[ sucℕ c ]) = refl
pf-incr (ϵ T[ c ]) = refl
pf-incr ((bs I[ zero ]) T[ c ]) = refl
pf-incr ((bs I[ sucℕ x ]) T[ c ]) = refl

pf-decr : ∀ s → pred (Skew⇒Nat s) ≡ Skew⇒Nat (decr s)
pf-decr ϵ = refl
pf-decr (ϵ I[ sucℕ c ]) = refl
pf-decr ((bs I[ x ]) I[ sucℕ c ]) = refl
pf-decr (ϵ I[ zero ]) = refl
pf-decr ((bs I[ c ]) I[ zero ]) = refl
pf-decr (x T[ zero ]) = refl
pf-decr (x T[ sucℕ x₁ ]) = refl

