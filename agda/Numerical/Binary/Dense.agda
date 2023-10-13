{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Relation.Binary.PropositionalEquality

module Numerical.Binary.Dense where

data Bin : Set where
  ϵ  : Bin
  _O : Bin → Bin
  _I : Bin → Bin

Bin⇒Nat-g : Bin → ℕ → ℕ
Bin⇒Nat-g ϵ k = 0
Bin⇒Nat-g (bs O) k =  0 {- * 2 ^ k + -} + Bin⇒Nat-g bs (1 + k)
Bin⇒Nat-g (bs I) k = {- 1 * -} 2 ^ k + Bin⇒Nat-g bs (1 + k)

Bin⇒Nat : Bin → ℕ
Bin⇒Nat b = Bin⇒Nat-g b 0

inc : Bin → Bin
inc ϵ = ϵ I
inc (bs O) = bs I
inc (bs I) = inc bs O

pf-inc-g : ∀ bs k → Bin⇒Nat-g (inc bs) k ≡ 2 ^ k + (Bin⇒Nat-g bs k)
pf-inc-g ϵ k = refl
pf-inc-g (bs O) k = refl
pf-inc-g (bs I) k rewrite pf-inc-g bs (suc k) = {!OK!}

pf-inc : ∀ bs → Bin⇒Nat (inc bs) ≡ suc (Bin⇒Nat bs)
pf-inc bs = pf-inc-g bs 0

dec : Bin → Bin
dec = {!!}

pf-dec : ∀ bs → Bin⇒Nat (dec bs) ≡ pred (Bin⇒Nat bs)
pf-dec bs = {!!}

add : Bin → Bin → Bin
add = {!!}

pf-add : ∀ bs₁ bs₂ → Bin⇒Nat (add bs₁ bs₂) ≡ (Bin⇒Nat bs₁) + (Bin⇒Nat bs₂)
pf-add bs₁ bs₂ = {!!}
