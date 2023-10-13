open import Data.Nat
open import Relation.Binary.PropositionalEquality

data Nat : Set where
  ϵ  : Nat
  _I : Nat → Nat

Nat⇒ℕ-g : Nat → ℕ → ℕ
Nat⇒ℕ-g ϵ k = 0
Nat⇒ℕ-g (bs I) k = {- 1 * -} 1 {- ^ k -} + Nat⇒ℕ-g bs (1 + k)

k-irrelevant : ∀ k → Nat⇒ℕ-g (((ϵ I) I) I) k ≡ 3
k-irrelevant k = refl
