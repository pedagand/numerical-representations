{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Product
open import Data.Nat
open import Data.Vec

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.HeterogeneousEquality hiding ([_])

-- From "Heterogeneous binary random-access lists", Swierstra and
-- "Programming with ornaments", Ko; suitably generalized (by myself)
-- to be container-independent

module Structure.Bin
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

  data DBin-g (A : Set) : ℕ → Set where
    ϵ : ∀ {n} → DBin-g A n
    _O : ∀ {n} → (bs : DBin-g A (suc n)) → DBin-g A n
    _[_]I : ∀{n} → (bs : DBin-g A (suc n))(t : T A n) → DBin-g A n

  DBin : Set → Set
  DBin A = DBin-g A 0

  open import Numerical.Bin

  forget : ∀ {A k} → DBin-g A k → Bin
  forget ϵ = ϵ
  forget (bs O) = (forget bs) O
  forget (bs [ t ]I) = (forget bs) I

  toVec-g : ∀ {A k} (t : DBin-g A k) → Vec A  (Bin⇒Nat-g (forget t) k)
  toVec-g ϵ = []
  toVec-g (bs O)  = toVec-g bs
  toVec-g (bs [ t ]I) = T-toVec t ++ toVec-g bs

  toVec : ∀ {A} (t : DBin A) → Vec A (Bin⇒Nat (forget t))
  toVec t = toVec-g t

  fromVec-g : ∀ {A k} b (vs : Vec A (Bin⇒Nat-g b k)) → DBin-g A k
  fromVec-g ϵ [] = ϵ
  fromVec-g (b O) vs = fromVec-g b vs O
  fromVec-g {k = k} (b I) vs with splitAt (2 ^ k) vs
  ... | (t , vs , _) = fromVec-g b vs [ T-fromVec k t ]I

  fromVec : ∀ {A} b (vs : Vec A (Bin⇒Nat b)) → DBin A
  fromVec b vs = fromVec-g b vs

  -- We expect the following:

  iso-to-from : ∀ {A} (t : DBin A) → fromVec (forget t) (toVec t) ≡ t
  iso-to-from = {!TO BE DONE!}

  iso-from-to : ∀ {A} b (vs : Vec A (Bin⇒Nat b)) → toVec (fromVec b vs) ≅ vs -- heterogeneous equality!
  iso-from-to = {!TO BE DONE!}
