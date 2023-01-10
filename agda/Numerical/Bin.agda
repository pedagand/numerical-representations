open import Data.Nat
open import Relation.Binary.PropositionalEquality

-- Binary numbers are the "numerical representation" underlying
-- various data-structures

-- Okasaki, Fig. 9.1, p.117
module Numerical.Bin where
  module Dense where
    data Bin : Set where
      ϵ  : Bin
      _O : Bin → Bin
      _I : Bin → Bin

    Bin⇒Nat-g : Bin → ℕ → ℕ
    Bin⇒Nat-g ϵ k = 0
    Bin⇒Nat-g (bs O) k = {- 0 * 2 ^ k + -} Bin⇒Nat-g bs (1 + k)
    Bin⇒Nat-g (bs I) k = {- 1 * -} 2 ^ k + Bin⇒Nat-g bs (1 + k)

    Bin⇒Nat : Bin → ℕ
    Bin⇒Nat b = Bin⇒Nat-g b 0

    inc : Bin → Bin
    inc ϵ = ϵ I
    inc (bs O) = bs I
    inc (bs I) = inc bs O

    pf-inc : ∀ bs → Bin⇒Nat (inc bs) ≡ suc (Bin⇒Nat bs)
    pf-inc bs = {!!}

    dec : Bin → Bin
    dec = {!!}

    pf-dec : ∀ bs → Bin⇒Nat (dec bs) ≡ pred (Bin⇒Nat bs)
    pf-dec bs = {!!}

    add : Bin → Bin → Bin
    add = {!!}

    pf-add : ∀ bs₁ bs₂ → Bin⇒Nat (add bs₁ bs₂) ≡ (Bin⇒Nat bs₁) + (Bin⇒Nat bs₂)
    pf-add bs₁ bs₂ = {!!}


  module Sparse where
    data Bin : Set where
      ϵ : Bin
      _I[_] : Bin → ℕ → Bin

    Bin⇒Nat-g : Bin → ℕ → ℕ
    Bin⇒Nat-g ϵ k = 0
    Bin⇒Nat-g (bs I[ c ]) k = {- 1 * -} 2 ^ (1 + c + k) + Bin⇒Nat-g bs (1 + c + k)

    Bin⇒Nat : Bin → ℕ
    Bin⇒Nat b = Bin⇒Nat-g b 0

    carry : Bin → Bin
    carry = {!!}

    borrow : Bin → Bin
    borrow = {!!}

    inc : Bin → Bin
    inc = {!!}

    dec : Bin → Bin
    dec = {!!}

    add : Bin → Bin → Bin
    add = {!!}
