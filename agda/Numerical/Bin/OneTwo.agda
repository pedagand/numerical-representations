{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])

module Numerical.Bin.OneTwo where

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

inc : OneTwo → OneTwo
inc ϵ = ϵ I
inc (b I) = b T
-- 2 + 2 * (OneTwo⇒Nat b) = 1 + 2 * (1 + OneTwo⇒Nat b)
--                        = 1 + 2 * (OneTwo⇒Nat (inc b))
inc (b T) = (inc b) I

valid-inc-g : ∀ b k → OneTwo⇒Nat-g (inc b) k ≡ 2 ^ k + OneTwo⇒Nat-g b k
valid-inc-g ϵ k = refl
valid-inc-g (b I) k = {!OK!}
valid-inc-g (b T) k rewrite valid-inc-g b (suc k) = {!OK!}

valid-inc : ∀ b → OneTwo⇒Nat (inc b) ≡ suc (OneTwo⇒Nat b)
valid-inc b = valid-inc-g b 0

canonicity-gen : ∀ b₁ b₂ k → OneTwo⇒Nat-g b₁ k ≡ OneTwo⇒Nat-g b₂ k → b₁ ≡ b₂
canonicity-gen ϵ ϵ k refl = refl
canonicity-gen ϵ (b₂ I) k q = {!q is empty!}
canonicity-gen ϵ (b₂ T) k q = {!q is empty!}
canonicity-gen (b₁ I) ϵ k q = {!q is empty!}
canonicity-gen (b₁ I) (b₂ I) k q rewrite canonicity-gen b₁ b₂ (suc k) {!OK!} = refl
canonicity-gen (b₁ I) (b₂ T) k q = {!!}
canonicity-gen (b₁ T) b₂ k q = {!!}

canonicity : ∀ b₁ b₂ → OneTwo⇒Nat b₁ ≡ OneTwo⇒Nat b₂ → b₁ ≡ b₂
canonicity = {!!}
