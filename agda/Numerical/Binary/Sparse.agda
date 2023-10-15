{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Fin renaming (suc to sucF) hiding (_+_ ; pred)
open import Data.Nat
open import Relation.Binary.PropositionalEquality

import Numerical.Generic.RunLength

module Numerical.Binary.Sparse where


base : ℕ → ℕ
base k = 2 ^ k

mode : Set
mode = ⊤

op : mode → ℕ
op m = 1

ar : ∀ {m} → Fin (op m) → ℕ
ar zero = 0

nx : ∀ {m} → Fin (op m) → mode
nx _ = tt

module Binary = Numerical.Generic.RunLength base mode op ar nx

open Binary

Bin = Num tt

Bin⇒Nat : Bin → ℕ
Bin⇒Nat = Binary.toℕ

Bin⇒Nat-help = toℕ-help

pattern _I[_] bs c = C zero c bs

-- Isomorphism with direct representation:

data Bin-View : Bin → Set where
  is-ϵ : Bin-View ϵ
  is-_I[_] : ∀ {bs} → Bin-View bs → (c : ℕ) → Bin-View (bs I[ c ])

Bin-view : ∀ bs → Bin-View bs
Bin-view ϵ = is-ϵ
Bin-view (bs I[ c ]) = is- Bin-view bs I[ c ]

-- Operations:

carry : Bin → Bin
carry = {!!}

borrow : Bin → Bin
borrow = {!!}

incr : Bin → Bin
incr = {!!}

decr : Bin → Bin
decr = {!!}

add : Bin → Bin → Bin
add = {!!}
