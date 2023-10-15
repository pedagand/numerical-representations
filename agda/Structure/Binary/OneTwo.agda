{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Product
open import Data.Fin renaming (suc to sucF)
open import Data.Nat
open import Data.Vec

open import Relation.Binary.PropositionalEquality

open import Numerical.Binary.OneTwo
import Structure.Generic.Dense

module Structure.Binary.OneTwo
    (T : Set → ℕ → Set)
    (T-toVec : ∀ {A k} → T A k → Vec A (2 ^ k))
    (T-fromVec : ∀ {A} k → Vec A (2 ^ k) → T A k)
    (T-iso-to-from : ∀ {A k} (t : T A k) → T-fromVec k (T-toVec t) ≡ t)
    (T-iso-from-to : ∀ {A} k (vs : Vec A (2 ^ k)) → T-toVec (T-fromVec k vs) ≡ vs)
   where

open Structure.Generic.Dense base mode op ar nx T T-toVec T-fromVec T-iso-to-from T-iso-from-to

DOneTwo : Set → ℕ → Set
DOneTwo A = Struc A tt

DOneTwo0 : Set → Set
DOneTwo0 A = Struc0 A tt

pattern _⟨_⟩I bs vs = C zero (vs ∷ []) bs
pattern _⟨_#_⟩T bs vs₁ vs₂ = C (sucF zero) (vs₁ ∷ vs₂ ∷ []) bs

data DOneTwo-View {A : Set} : ∀ {k : ℕ} → DOneTwo A k → Set where
  is-ϵ : ∀ {k} → DOneTwo-View (ϵ {k = k})
  is-_⟨_⟩I : ∀ {k}{bs : DOneTwo A (suc k)} →
             DOneTwo-View bs → (vs : T A k) → DOneTwo-View (bs ⟨ vs ⟩I)
  is-_⟨_#_⟩T : ∀ {k}{bs : DOneTwo A (suc k)} →
               DOneTwo-View bs → (vs₁ : T A k)(vs₂ : T A k) →
               DOneTwo-View (bs ⟨ vs₁ # vs₂ ⟩T)

DOneTwo-view : ∀ {A k} → (bs : DOneTwo A k) → DOneTwo-View bs
DOneTwo-view ϵ = is-ϵ
DOneTwo-view (bs ⟨ vs ⟩I) = is- DOneTwo-view bs ⟨ vs ⟩I
DOneTwo-view (bs ⟨ vs₁ # vs₂ ⟩T) = is- DOneTwo-view bs ⟨ vs₁ # vs₂ ⟩T
