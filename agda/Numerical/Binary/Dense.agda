{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Fin renaming (suc to sucF) hiding (_+_ ; pred)
open import Data.Nat
open import Relation.Binary.PropositionalEquality

import Numerical.Generic.Dense

module Numerical.Binary.Dense where

base : ℕ → ℕ
base k = 2 ^ k

mode : Set
mode = ⊤

op : mode → ℕ
op m = 2

ar : ∀ {m} → Fin (op m) → ℕ
ar zero = 0
ar (sucF zero) = 1

nx : ∀ {m} → Fin (op m) → mode
nx _ = tt

module Binary = Numerical.Generic.Dense base mode op ar nx

open Binary

Bin = Num tt

Bin⇒Nat : Bin → ℕ
Bin⇒Nat = Binary.toℕ

Bin⇒Nat-help = toℕ-help

pattern _O bs = C zero bs
pattern _I bs = C (sucF zero) bs

-- Isomorphism with direct representation:

data Bin-View : Bin → Set where
  is-ϵ  : Bin-View ϵ
  is-_O : ∀ {bs} → Bin-View bs → Bin-View (bs O)
  is-_I : ∀ {bs} → Bin-View bs → Bin-View (bs I)

Bin-view : ∀ bs → Bin-View bs
Bin-view ϵ = is-ϵ
Bin-view (bs O) = is- Bin-view bs O
Bin-view (bs I) = is- Bin-view bs I

-- Operations:

incr : Bin → Bin
incr ϵ = ϵ I
incr (bs O) = bs I
incr (bs I) = incr bs O

decr : Bin → Bin
decr = {!!}

add : Bin → Bin → Bin
add = {!!}

-- Properties:

pf-incr-g : ∀ bs k → Bin⇒Nat-help (incr bs) k ≡ 2 ^ k + (Bin⇒Nat-help bs k)
pf-incr-g ϵ k = {!!} {- TRUE: refl -}
pf-incr-g (bs O) k = {!!} {- TRUE: refl -}
pf-incr-g (bs I) k rewrite pf-incr-g bs (suc k) = {!OK!}

pf-incr : ∀ bs → Bin⇒Nat (incr bs) ≡ suc (Bin⇒Nat bs)
pf-incr bs = pf-incr-g bs 0

pf-decr : ∀ bs → Bin⇒Nat (decr bs) ≡ pred (Bin⇒Nat bs)
pf-decr bs = {!!}

pf-add : ∀ bs₁ bs₂ → Bin⇒Nat (add bs₁ bs₂) ≡ (Bin⇒Nat bs₁) + (Bin⇒Nat bs₂)
pf-add bs₁ bs₂ = {!!}
