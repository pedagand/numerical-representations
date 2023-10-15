{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Fin hiding (_+_ ; pred) renaming (suc to sucF)
open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import Numerical.Nat.Properties

import Numerical.Generic.Dense

module Numerical.SkewBinary.Dense where

base : ℕ → ℕ
base k = 2^[ k +1]-1

mode : Set
mode = ⊤

op : mode → ℕ
op m = 3

ar : ∀ {m} → Fin (op m) → ℕ
ar zero = 0
ar (sucF zero) = 1
ar (sucF (sucF zero)) = 2

nx : ∀ {m} → Fin (op m) → mode
nx _ = tt

module SkewBinary = Numerical.Generic.Dense base mode op ar nx

open SkewBinary

Skew = Num tt

Skew⇒Nat : Skew → ℕ
Skew⇒Nat = SkewBinary.toℕ

Skew⇒Nat-help = toℕ-help

pattern _O bs = C zero bs
pattern _I bs = C (sucF zero) bs
pattern _T bs = C (sucF (sucF zero)) bs

_ : Skew⇒Nat (ϵ O) ≡ 0
_ = refl

_ : Skew⇒Nat (ϵ I) ≡ 1
_ = refl

_ : Skew⇒Nat (ϵ T) ≡ 2
_ = refl

_ : Skew⇒Nat (ϵ I O) ≡ 3
_ = refl

_ : Skew⇒Nat (ϵ I I) ≡ 4
_ = refl

_ : Skew⇒Nat (ϵ I T) ≡ 5
_ = refl

_ : Skew⇒Nat (ϵ T O) ≡ 6
_ = refl

_ : Skew⇒Nat (ϵ I O O) ≡ 7
_ = refl

_ : Skew⇒Nat (ϵ I O O O) ≡ 15
_ = refl

_ : Skew⇒Nat (ϵ T O I) ≡ 15
_ = refl

_ : Skew⇒Nat (ϵ I T T) ≡ 15
_ = refl


-- Isomorphism with direct representation:

data Skew-View : Skew → Set where
  is-ϵ  : Skew-View ϵ
  is-_O : ∀ {bs} → Skew-View bs → Skew-View (bs O)
  is-_I : ∀ {bs} → Skew-View bs → Skew-View (bs I)
  is-_T : ∀ {bs} → Skew-View bs → Skew-View (bs T)

Skew-view : ∀ bs → Skew-View bs
Skew-view ϵ = is-ϵ
Skew-view (bs O) = is- Skew-view bs O
Skew-view (bs I) = is- Skew-view bs I
Skew-view (bs T) = is- Skew-view bs T

-- Operations:

-- Remark: this cannot be implemented in constant-time because
--
--   1. we have Os lying getting in the way (case `n O`)
--   2. we have carries that could propgate (case `n T T`)
--
-- which makes this representation useless for the intended
-- data-structure
incr : Skew → Skew
incr ϵ = ϵ I
incr (n O) = n I
incr (n I) = n T
incr (ϵ T) = {!!}
incr ((n O) T) = n I O
incr ((n I) T) = n T O
incr ((n T) T) = {!!}


pf-incr-g : ∀ k n → Skew⇒Nat-help (incr n) k ≡ 2^[ k +1]-1 * (suc (Skew⇒Nat-help n k))
pf-incr-g k ϵ = {!TRUE!}
pf-incr-g k (n O) = {!TRUE!}
pf-incr-g k (n I) = {!!}
pf-incr-g k (ϵ T) = {!!}
pf-incr-g k ((n O) T) = {!!}
pf-incr-g k ((n I) T) = {!!}
pf-incr-g k ((n T) T) = {!!}

pf-incr : ∀ n → Skew⇒Nat (incr n) ≡ suc (Skew⇒Nat n)
pf-incr n rewrite pf-incr-g 0 n = {!TRUE!}
