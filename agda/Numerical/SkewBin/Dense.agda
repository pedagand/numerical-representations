open import Data.Nat renaming (suc to sucℕ)

open import Relation.Binary.PropositionalEquality

open import Utils

module SkewBin.Dense where

data Skew : Set where
  ϵ  : Skew
  _O : Skew → Skew
  _I : Skew → Skew
  _T : Skew → Skew

Skew⇒Nat-g : Skew → ℕ → ℕ
Skew⇒Nat-g ϵ k = 0
Skew⇒Nat-g (bs O) k = {- 0 * 2^[ k +1]-1 + -} Skew⇒Nat-g bs (1 + k)
Skew⇒Nat-g (bs I) k = {- 1 * -} 2^[ k +1]-1 + Skew⇒Nat-g bs (1 + k)
Skew⇒Nat-g (bs T) k = {- 2 * 2^[ k +1]-1 = -} 2^[ k +1]-1 + 2^[ k +1]-1 + Skew⇒Nat-g bs (1 + k)

Skew⇒Nat : Skew → ℕ
Skew⇒Nat b = Skew⇒Nat-g b 0

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


-- XXX: this cannot be implemented in constant-time because
--
--   1. we have Os lying getting in the way (case `n O`)
--   2. we have carries that could propgate (case `n T T`)
--
-- which makes this representation useless for the intended
-- data-structure
suc : Skew → Skew
suc ϵ = ϵ I
suc (n O) = n I
suc (n I) = n T
suc (ϵ T) = {!!}
suc ((n O) T) = n I O
suc ((n I) T) = n T O
suc ((n T) T) = {!!}


pf-suc-g : ∀ k n → Skew⇒Nat-g (suc n) k ≡ 2^[ k +1]-1 * (sucℕ (Skew⇒Nat-g n k))
pf-suc-g k ϵ = {!TRUE!}
pf-suc-g k (n O) = {!TRUE!}
pf-suc-g k (n I) = {!!}
pf-suc-g k (ϵ T) = {!!}
pf-suc-g k ((n O) T) = {!!}
pf-suc-g k ((n I) T) = {!!}
pf-suc-g k ((n T) T) = {!!}

pf-suc : ∀ n → Skew⇒Nat (suc n) ≡ sucℕ (Skew⇒Nat n)
pf-suc n rewrite pf-suc-g 0 n = {!TRUE!}
