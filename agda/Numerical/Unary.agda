open import Data.Unit
open import Data.Fin
open import Data.Nat
open import Relation.Binary.PropositionalEquality
import Numerical.Generic.Dense

module Numerical.Unary where

base : ℕ → ℕ
base _ = 1

mode : Set
mode = ⊤

op : mode → ℕ
op _ = 1

ar : ∀ {m} → Fin (op m) → ℕ
ar zero = 1

nx : ∀ {m} → Fin (op m) → mode
nx _ = tt

open Numerical.Generic.Dense base mode op ar nx

Nat = Num tt
Nat⇒ℕ = Numerical.Generic.Dense.toℕ

data Nat-View : Nat → Set where
  ϵ  : Nat-View ϵ
  _I : ∀ {n} → Nat-View n → Nat-View (C zero n)

Nat-view : ∀ n → Nat-View n
Nat-view ϵ = ϵ
Nat-view (C zero n) with Nat-view n
... | k = k I
