{-# OPTIONS --rewriting #-}

open import Data.Nat renaming (suc to sucℕ)
open import Relation.Binary.PropositionalEquality

open import Numerical.Nat.Properties

{-# BUILTIN REWRITE _≡_ #-}

module Numerical.SkewBinary.SparseCanonical where

    data Mode : Set where
      I C : Mode

    data Skew : Mode → Set where
      ϵ  : ∀ {m} → Skew m
      _I[_] : ∀ {m} → Skew I → ℕ → Skew m
      _T[_] : Skew I → ℕ → Skew C

    Skew⇒Nat-g : ∀ {m} → Skew m → ℕ → ℕ
    Skew⇒Nat-g ϵ k = 0
    Skew⇒Nat-g (bs I[ c ]) k =
       {- 1 * -} 2^[ k + c +1]-1
      + Skew⇒Nat-g bs (1 + k + c)
    Skew⇒Nat-g (bs T[ c ]) k =
      {- 2 * 2^[ k +1]-1 = -}
       2^[ c +1]-1 + 2^[ c +1]-1
      + Skew⇒Nat-g bs (1 + c)

    Skew⇒Nat : Skew C → ℕ
    Skew⇒Nat bs = Skew⇒Nat-g bs 0

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


    incr : Skew C → Skew C
    incr ϵ = ϵ I[ 0 ]
    incr (bs I[ 0 ]) = bs T[ 0 ]
    incr (bs I[ sucℕ c ]) = bs I[ c ] I[ 0 ]
    incr (ϵ T[ c ]) = ϵ I[ sucℕ c ]
    incr (bs I[ zero ] T[ c ]) = bs T[ sucℕ c ]
    incr (bs I[ sucℕ c₁ ] T[ c ]) = bs I[ c₁ ] I[ sucℕ c ]

    Nat⇒Skew : ℕ → Skew C
    Nat⇒Skew zero = ϵ
    Nat⇒Skew (sucℕ n) = incr (Nat⇒Skew n)

    decr : Skew C → Skew C
    decr ϵ = ϵ
    decr (ϵ I[ sucℕ c ]) = ϵ T[ c ]
    decr ((bs I[ c₁ ]) I[ sucℕ c ]) = bs I[ sucℕ c₁ ]  T[ c ]
    decr (ϵ I[ zero ]) = ϵ
    decr ((bs I[ c ]) I[ zero ]) = bs I[ sucℕ c ]
    decr (bs T[ zero ]) = bs I[ zero ]
    decr (bs T[ sucℕ c ]) = bs I[ 0 ] T[ c ]

    rewrite-+0 : ∀ n → n + 0 ≡ n
    rewrite-+0 zero = refl
    rewrite-+0 (sucℕ n) rewrite rewrite-+0 n = refl

    rewrite-+S : ∀ n m → n + sucℕ m ≡ sucℕ (n + m)
    rewrite-+S zero m = refl
    rewrite-+S (sucℕ n) m rewrite rewrite-+S n m = refl

    rewrite-+-comm : ∀ m n o → m + (n + o) ≡ m + n + o
    rewrite-+-comm zero n o = refl
    rewrite-+-comm (sucℕ m) n o rewrite rewrite-+-comm m n o = refl

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
