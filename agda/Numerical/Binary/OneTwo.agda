{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Fin renaming (suc to sucF) hiding (_+_ ; pred)
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])

import Numerical.Generic.Dense

module Numerical.Binary.OneTwo where

base : ℕ → ℕ
base k = 2 ^ k

mode : Set
mode = ⊤

op : mode → ℕ
op m = 2

ar : ∀ {m} → Fin (op m) → ℕ
ar zero = 1
ar (sucF zero) = 2

nx : ∀ {m} → Fin (op m) → mode
nx _ = tt

module Binary = Numerical.Generic.Dense base mode op ar nx

open Binary

OneTwo = Num tt

OneTwo⇒Nat : OneTwo → ℕ
OneTwo⇒Nat = Binary.toℕ

OneTwo⇒Nat-help = toℕ-help

pattern _I bs = C zero bs
pattern _T bs = C (sucF zero) bs

-- Isomorphism with direct representation:

data OneTwo-View : OneTwo → Set where
  is-ϵ  : OneTwo-View ϵ
  is-_I : ∀ {bs} → OneTwo-View bs → OneTwo-View (bs I)
  is-_T : ∀ {bs} → OneTwo-View bs → OneTwo-View (bs T)

OneTwo-view : ∀ bs → OneTwo-View bs
OneTwo-view ϵ = is-ϵ
OneTwo-view (bs I) = is- (OneTwo-view bs) I
OneTwo-view (bs T) = is- (OneTwo-view bs) T

-- Operations:

incr : OneTwo → OneTwo
incr ϵ = ϵ I
incr (b I) = b T
-- 2 + 2 * (OneTwo⇒Nat b) = 1 + 2 * (1 + OneTwo⇒Nat b)
--                        = 1 + 2 * (OneTwo⇒Nat (incr b))
incr (b T) = (incr b) I

valid-incr-g : ∀ b k → OneTwo⇒Nat-help (incr b) k ≡ 2 ^ k + OneTwo⇒Nat-help b k
valid-incr-g ϵ k = {!OK!} 
valid-incr-g (b I) k = {!OK!}
valid-incr-g (b T) k rewrite valid-incr-g b (suc k) = {!OK!}

valid-incr : ∀ b → OneTwo⇒Nat (incr b) ≡ suc (OneTwo⇒Nat b)
valid-incr b = valid-incr-g b 0

canonicity-gen : ∀ b₁ b₂ k → OneTwo⇒Nat-help b₁ k ≡ OneTwo⇒Nat-help b₂ k → b₁ ≡ b₂
canonicity-gen ϵ ϵ k refl = refl
canonicity-gen ϵ (b₂ I) k q = {!q is empty!}
canonicity-gen ϵ (b₂ T) k q = {!q is empty!}
canonicity-gen (b₁ I) ϵ k q = {!q is empty!}
canonicity-gen (b₁ I) (b₂ I) k q rewrite canonicity-gen b₁ b₂ (suc k) {!OK!} = refl
canonicity-gen (b₁ I) (b₂ T) k q = {!!}
canonicity-gen (b₁ T) b₂ k q = {!!}

canonicity : ∀ b₁ b₂ → OneTwo⇒Nat b₁ ≡ OneTwo⇒Nat b₂ → b₁ ≡ b₂
canonicity = {!!}

