open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Vec

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.HeterogeneousEquality hiding ([_])

{-

From

  "Numerical representation as higher-order nested datatypes", Hinze

in Haskell with nested types:

 > data Fork t a = Fork (t a) (t a)
 >
 > data RandomAccessList bush a =
 >  | Nil
 >  | Zero (RandomAccessList (Fork bush) a)
 >  | One (bush a) (RandomAccessList (Fork bush) a)

 > data Id a = Id a
 > data IxSequence a = RandomAccessList Id a

-}

module BinaryRandomAccessList where

  -- 1. Binary numbers are the "numerical representation" underlying
  -- the binary random access list data-structure.

  module NumericalRepresentation where


    data Bin : Set where
      ϵ  : Bin
      _O : Bin → Bin
      _I : Bin → Bin

    Bin⇒Nat-g : Bin → ℕ → ℕ
    Bin⇒Nat-g ϵ k = 0
    Bin⇒Nat-g (bs O) k = {- 0 * 2 ^ k + -} Bin⇒Nat-g bs (1 + k)
    Bin⇒Nat-g (bs I) k = {- 1 * -} 2 ^ k + Bin⇒Nat-g bs (1 + k)

    Bin⇒Nat : Bin → ℕ
    Bin⇒Nat b = Bin⇒Nat-g b 0

  -- 2. "Heterogeneous binary random-access lists", Swierstra
  -- suitably generalized (by myself) to be container-independent

  module Datastructure
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

    data RALg (A : Set) : ℕ → Set where
      ϵ : ∀ {n} → RALg A n
      _O : ∀ {n} → (bs : RALg A (suc n)) → RALg A n
      _[_]I : ∀{n} → (bs : RALg A (suc n))(t : T A n) → RALg A n

    RAL : Set → Set
    RAL A = RALg A 0

    open NumericalRepresentation

    forget : ∀ {A k} → RALg A k → Bin
    forget ϵ = ϵ
    forget (bs O) = (forget bs) O
    forget (bs [ t ]I) = (forget bs) I

    toVec-g : ∀ {A k} (t : RALg A k) → Vec A  (Bin⇒Nat-g (forget t) k)
    toVec-g ϵ = []
    toVec-g (bs O)  = toVec-g bs
    toVec-g (bs [ t ]I) = T-toVec t ++ toVec-g bs

    toVec : ∀ {A} (t : RAL A) → Vec A (Bin⇒Nat (forget t))
    toVec t = toVec-g t

    fromVec-g : ∀ {A k} b (vs : Vec A (Bin⇒Nat-g b k)) → RALg A k
    fromVec-g ϵ [] = ϵ
    fromVec-g (b O) vs = fromVec-g b vs O
    fromVec-g {k = k} (b I) vs with splitAt (2 ^ k) vs
    ... | (t , vs , _) = fromVec-g b vs [ T-fromVec k t ]I

    fromVec : ∀ {A} b (vs : Vec A (Bin⇒Nat b)) → RAL A
    fromVec b vs = fromVec-g b vs

    -- We expect the following:

    iso-to-from : ∀ {A} (t : RAL A) → fromVec (forget t) (toVec t) ≡ t
    iso-to-from = {!TO BE DONE!}

    iso-from-to : ∀ {A} b (vs : Vec A (Bin⇒Nat b)) → toVec (fromVec b vs) ≅ vs -- heterogeneous equality!
    iso-from-to = {!TO BE DONE!}

    -- TODO: implement all the operations on the datastructure:
    --   cf. "Numerical representation as higher-order nested datatypes", Fig. 3, p.13 for the interface
    --   cf. Okasaki, Sec. 9.2.1 and 10.1.2 for the implementation

    -- empty : RAL A
    -- cons : A → RAL A → RAL A
    -- front : RAL A → A × RAL A
    -- snoc : RAL A → A → RAL A
    -- rear : RAL A → A × RAL A
    -- access : RAL A → ℕ → Maybe A
    -- update : RAL A → ℕ → A → RAL A


  -- 3. A particular, suitably size container to implement the `T`
  -- interface of the `Datastructure` module. Here: complete leaf
  -- binary tree.

  module Container where

    data Tree (A : Set) : ℕ → Set where
      Leaf : A → Tree A 0
      Node : ∀ {n} → Tree A n → Tree A n → Tree A (suc n)

    toVec : ∀ {A k} → Tree A k → Vec A (2 ^ k)
    toVec (Leaf x) = [ x ]
    toVec (Node t₁ t₂) = toVec t₁ ++ toVec t₂ ++ []

    fromVec : ∀ {A} k → Vec A (2 ^ k) → Tree A k
    fromVec zero (a ∷ []) = Leaf a
    fromVec (suc k) vs with splitAt (2 ^ k) vs
    ... | (ls , rs , _ ) with splitAt (2 ^ k) rs
    ... | (rs , _ , _) = Node (fromVec k ls) (fromVec k rs)

    iso-to-from : ∀ {A k} (t : Tree A k) → fromVec k (toVec t) ≡ t
    iso-to-from = {!TO BE DONE!}

    iso-from-to : ∀ {A} k (vs : Vec A (2 ^ k)) → toVec (fromVec k vs) ≡ vs
    iso-from-to = {!TO BE DONE!}


  -- 4. Composing `Datastructure` with `Container` to obtain the desired datatype

  bRAL : Set → Set
  bRAL A = Datastructure.RAL Container.Tree
                             Container.toVec Container.fromVec
                             Container.iso-to-from Container.iso-from-to A
