open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (_+_ ; toℕ)
open import Data.Vec renaming (map to map-Vec ; sum to sum-Vec)
open import Data.Product renaming (map to map×)
open import Data.Sum renaming (map to mapΣ)
open import Relation.Binary.PropositionalEquality

module Generic where
  module G
      -- Choose a numerical base:
      (base : ℕ → ℕ)
      -- Choose a numerical repr:
      (mode : Set)
      (op : mode → ℕ)
      (ar : ∀ {m} → Fin (op m) → ℕ)
      (nx : ∀ {m} → Fin (op m) → mode)
    where

    data Num (A : ℕ → Set) : mode → Set where
      ϵ : ∀ {m} → Num A m
      C : ∀ {m} → (d : Fin (op m))(as : Vec (A {!!}) (suc (ar d)))(c : ℕ) → Num A (nx d) → Num A m

    val : ∀ {A : Set}{m}{d : Fin (op m)} → Vec A (suc (ar d)) → ℕ → ℕ
    val as k = Data.Vec.sum (Data.Vec.map (λ _ → base k) as)

    toℕ-help : ∀ {A m} → Num A m → ℕ → ℕ
    toℕ-help ϵ k = 0
    toℕ-help (C d as c n) k = val as (k + c) + toℕ-help n (1 + k + c)

    toℕ : ∀ {A m} → Num A m → ℕ
    toℕ n = toℕ-help n 0

    -- valid-Num-help : ∀ {A m}→ Num (T A) m → ℕ → Set
    -- valid-Num-help ϵ k = ⊤
    -- valid-Num-help (C x c a) k = sum (map size x) ≡ val x (k + c) × valid-Num-help a (1 + k + c) 

  {-
  -- XXX: Not RLE
  module OneTwoSig where
    mode : Set
    mode = ⊤
  
    op : mode → ℕ
    op tt = 2

    ar : ∀ {tt} → Fin (op tt) → ℕ
    ar zero = 1
    ar (suc zero) = 2

    base : ℕ → ℕ
    base k = 2 ^ k

    {-
    data Tree (A : Set) : Set where
      Leaf : A → Tree A
      Node : Tree A → Tree A → Tree A

    size : ∀ {A} → Tree A → ℕ
    size (Leaf x) = 1
    size (Node t₁ t₂) = size t₁ + size t₂ 
    -}

  module OneTwo = G OneTwoSig.base OneTwoSig.mode OneTwoSig.op OneTwoSig.ar 

  open OneTwo

  pattern _[_]I bs t = C (inj₁ t) bs
  pattern _[_#_]T bs t₀ t₁ = C (inj₂ (t₀ , t₁)) bs
  -}
  
  module SkewSig where
    data mode : Set where
      C I : mode
  
    op : mode → ℕ
    op m = suc (op2 m)
      where op2 : mode → ℕ
            op2 C = 1
            op2 I = 0

    ar : ∀ {m} → Fin (op m) → ℕ
    ar zero = 0
    ar {C} (suc zero) = 1

    nx : ∀ {m} → Fin (op m) → mode
    nx zero = I
    nx {C} (suc zero) = I

    2^[_+1]-1 : ℕ → ℕ
    2^[ zero +1]-1 = 1
    2^[ suc k +1]-1 = suc (n + n)
       where n = 2^[ k +1]-1

    base : ℕ → ℕ
    base k = 2^[ k +1]-1

    {-
    data Tree (A : Set) : Set where
      Leaf : Tree A
      Node : Tree A → A → Tree A → Tree A

    size : ∀ {A} → Tree A → ℕ
    size Leaf  = 0
    size (Node t₁ a t₂) = 1 + size t₁ + size t₂ 
    -}


  module Skew = G SkewSig.base SkewSig.mode SkewSig.op SkewSig.ar SkewSig.nx

  open Skew

  data Skew-View : ∀ {m} → Num (λ _ → ⊤) m → Set where
    ϵ : ∀ {m} → Skew-View {m} ϵ
    _I[_] : ∀ {m} (bs : Num (λ _ → ⊤) SkewSig.I)(c : ℕ) →
            Skew-View {m} (G.C zero (tt ∷ []) c bs)
    _T[_] : (bs : Num (λ _ → ⊤) SkewSig.I)(c : ℕ) →
            Skew-View {SkewSig.C} (G.C (suc zero)  (tt ∷ tt ∷ []) c bs)

  Skew-view : ∀ {m} → (bs : Num (λ _ → ⊤) m) → Skew-View bs
  Skew-view {m} G.ϵ = ϵ
  Skew-view {m} (G.C zero (tt ∷ []) c bs) = bs I[ c ]
  Skew-view {SkewSig.C} (G.C (suc zero) (tt ∷ tt ∷ []) c bs) = bs T[ c ]

  
  
  incr : ∀ {m} → Num (λ _ → ⊤) m → Num (λ _ → ⊤) SkewSig.I
  incr bs with Skew-view bs
  ... | ϵ = {!!}
  ... | bs I[ c ] = {!!}
  ... | bs T[ c ] = {!!}
