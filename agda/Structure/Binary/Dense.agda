{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Product
open import Data.Fin renaming (suc to sucF)
open import Data.Nat
open import Data.Vec

open import Relation.Binary.PropositionalEquality

open import Numerical.Binary.Dense hiding (_O ; _I)
import Structure.Generic.Dense

-- From "Heterogeneous binary random-access lists", Swierstra and
-- "Programming with ornaments", Ko; suitably generalized (by myself)
-- to be container-independent

module Structure.Binary.Dense
    (T : Set → ℕ → Set)
    (T-toVec : ∀ {A k} → T A k → Vec A (2 ^ k))
    (T-fromVec : ∀ {A} k → Vec A (2 ^ k) → T A k)
    (T-iso-to-from : ∀ {A k} (t : T A k) → T-fromVec k (T-toVec t) ≡ t)
    (T-iso-from-to : ∀ {A} k (vs : Vec A (2 ^ k)) → T-toVec (T-fromVec k vs) ≡ vs)
   where

open Structure.Generic.Dense base mode op ar nx T T-toVec T-fromVec T-iso-to-from T-iso-from-to

DBin : Set → ℕ → Set
DBin A = Struc A tt

DBin0 : Set → Set
DBin0 A = Struc0 A tt


pattern _O bs = C zero [] bs
pattern _⟨_⟩I bs vs = C (sucF zero) (vs ∷ []) bs

-- Isomorphism with direct representation:

data DBin-View {A : Set} : ∀ {k} → DBin A k → Set where
  is-ϵ : ∀ {k} → DBin-View (ϵ {k = k})
  is-_O : ∀ {k}{bs : DBin A (suc k)} → DBin-View bs → DBin-View (bs O)
  is-_⟨_⟩I : ∀{k}{bs : DBin A (suc k)} → DBin-View bs → (vs : T A k) → DBin-View (bs ⟨ vs ⟩I)

DBin-view : ∀ {A k} (bs : DBin A k) → DBin-View bs
DBin-view ϵ = is-ϵ
DBin-view (bs O) = is- DBin-view bs O
DBin-view (bs ⟨ vs ⟩I) = is- DBin-view bs ⟨ vs ⟩I
