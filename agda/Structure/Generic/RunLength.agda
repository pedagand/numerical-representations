open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (_+_ ; splitAt) renaming (toℕ to Fin-toℕ)
open import Data.Vec renaming (map to map-Vec ; sum to sum-Vec)
open import Data.Product renaming (map to map×)
open import Data.Sum renaming (map to mapΣ)

open import Relation.Binary.PropositionalEquality

module Structure.Generic.RunLength
      -- Choose a numerical base:
      (base : ℕ → ℕ)
      -- Choose a numerical repr:
      (mode : Set)
      (op : mode → ℕ)
      (ar : ∀ {m} → Fin (op m) → ℕ)
      (nx : ∀ {m} → Fin (op m) → mode)
      -- Choose a container
      (T : Set → ℕ → Set)
      (T-toVec : ∀ {A k} → T A k → Vec A (base k))
      (T-fromVec : ∀ {A} k → Vec A (base k) → T A k)
      (T-iso-to-from : ∀ {A k} (t : T A k) → T-fromVec k (T-toVec t) ≡ t)
      (T-iso-from-to : ∀ {A} k (vs : Vec A (base k)) → T-toVec (T-fromVec k vs) ≡ vs)
    where

-- This is an algebraic ornament of Numerical.Generic.RunLength.toℕ over
-- Numerical.Generic.RunLength.Num together with an ornament inserting `T
-- A k`
data Struc (A : Set) : mode → ℕ → Set where
  ϵ : ∀ {m k} → Struc A m k
  C : ∀ {m k} → (d : Fin (op m))(c : ℕ)(vs : Vec (T A (k + c)) (suc (ar d))) → Struc A (nx d) (1 + k + c) → Struc A m k

Struc0 : Set → mode → Set
Struc0 A m = Struc A m 0

open import Numerical.Generic.RunLength base mode op ar nx

toNum : ∀ {A m k} → Struc A m k → Num m
toNum ϵ = ϵ
toNum (C d c vs s) = C d c (toNum s)

toVec-help : ∀ {A m k} (t : Struc A m k) → Vec A (toℕ-help (toNum t) k)
toVec-help ϵ = []
toVec-help (C d c vs t) = concat (Data.Vec.map T-toVec vs) ++ toVec-help t

toVec : ∀ {A m} (t : Struc0 A m) → Vec A (toℕ (toNum t))
toVec t = toVec-help t

fromVec-help : ∀ {A m k} (b : Num m) (vs : Vec A (toℕ-help b k)) → Struc A m k
fromVec-help ϵ [] = ϵ
fromVec-help {k = k} (C d c bs) vs with splitAt ((suc (ar d)) * base (k + c)) vs
... | (v1 , v2 , refl) with group (suc (ar d)) (base (k + c)) v1
... | (vss , refl) = C d c (Data.Vec.map (T-fromVec (k + c)) vss) (fromVec-help bs v2)

fromVec : ∀ {A m} (b : Num m) (vs : Vec A (toℕ b)) → Struc0 A m
fromVec b vs = fromVec-help b vs


-- iso-to-from : ∀ {A} (t :  A) → fromVec (forget t) (toVec t) ≡ t
-- iso-to-from = {!TO BE DONE!}

-- iso-from-to : ∀ {A} b (vs : Vec A (Bin⇒Nat b)) → toVec (fromVec b vs) ≅ vs -- heterogeneous equality!
-- iso-from-to = {!TO BE DONE!}

