{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Product
open import Data.Nat
open import Data.Vec

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.HeterogeneousEquality hiding ([_])

module Structure.OneTwo
    (T : Set → ℕ → Set)
    (T-toVec : ∀ {A k} → T A k → Vec A (2 ^ k))
    (T-fromVec : ∀ {A} k → Vec A (2 ^ k) → T A k)
    (T-iso-to-from : ∀ {A k} (t : T A k) → T-fromVec k (T-toVec t) ≡ t)
    (T-iso-from-to : ∀ {A} k (vs : Vec A (2 ^ k)) → T-toVec (T-fromVec k vs) ≡ vs)
   where

  -- `T` is any container of the right size

  -- Remark (1): instead of `T-toVec`, one could have asked for

  --   T-toList : ∀ {A k} → T A k → List A
  --   T-pf-size : ∀ {A k} → (t : T A k) → length t ≡ 2 ^k

  -- Similarly for `T-fromVec`, we could ask for any list *of the
  -- suitable size*.

  data DOneTwo-g (A : Set) : ℕ → Set where
    ϵ : ∀ {n} → DOneTwo-g A n
    _[_]I : ∀ {n} → (bs : DOneTwo-g A (suc n))(t : T A n) → DOneTwo-g A n
    _[_#_]T : ∀{n} → (bs : DOneTwo-g A (suc n))(t₀ : T A n)(t₁ : T A n) → DOneTwo-g A n

  DOneTwo : Set → Set
  DOneTwo A = DOneTwo-g A 0

  open import Numerical.OneTwo

  forget : ∀ {A k} → DOneTwo-g A k → OneTwo
  forget ϵ = ϵ
  forget (bs [ t ]I) = (forget bs) I
  forget (bs [ t₀ # t₁ ]T) = _T (forget bs)

  toVec-g : ∀ {A k} (t : DOneTwo-g A k) → Vec A  (OneTwo⇒Nat-g (forget t) k)
  toVec-g ϵ = []
  toVec-g (bs [ t ]I) = T-toVec t ++ toVec-g bs
  toVec-g (bs [ t₀ # t₁ ]T) = (T-toVec t₀ ++ T-toVec t₁) ++ toVec-g bs

  toVec : ∀ {A} (t : DOneTwo A) → Vec A (OneTwo⇒Nat (forget t))
  toVec t = toVec-g t

  fromVec-g : ∀ {A k} b (vs : Vec A (OneTwo⇒Nat-g b k)) → DOneTwo-g A k
  fromVec-g ϵ [] = ϵ
  fromVec-g {k = k} (b I) vs with splitAt (2 ^ k) vs
  ... | (t , vs , _) = fromVec-g b vs [ T-fromVec k t ]I
  fromVec-g {k = k} (b T) vs with splitAt (2 ^ k + 2 ^ k) vs
  ... | (ls , vs , _) with splitAt (2 ^ k) ls
  ... | (ls , rs , _) = fromVec-g b vs [ T-fromVec k ls # T-fromVec k rs ]T

  fromVec : ∀ {A} b (vs : Vec A (OneTwo⇒Nat b)) → DOneTwo A
  fromVec b vs = fromVec-g b vs

  -- We expect the following:

  iso-to-from : ∀ {A} (t : DOneTwo A) → fromVec (forget t) (toVec t) ≡ t
  iso-to-from = {!TO BE DONE!}

  iso-from-to : ∀ {A} b (vs : Vec A (OneTwo⇒Nat b)) → toVec (fromVec b vs) ≅ vs -- heterogeneous equality!
  iso-from-to = {!TO BE DONE!}
