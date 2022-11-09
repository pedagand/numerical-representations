{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product 
open import Data.Maybe
open import Data.Fin using (fromℕ<)
open import Data.Vec hiding (head ; tail)
open import Function
open import Relation.Nullary

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

  -- Composing 01-binary structure with leaf binary tree

  open import Structure.Bin
  open import Container.LeafBinaryTree

  RAL-g : Set → ℕ → Set
  RAL-g A n = DBin-g Tree 
               Container.LeafBinaryTree.toVec Container.LeafBinaryTree.fromVec
               Container.LeafBinaryTree.iso-to-from Container.LeafBinaryTree.iso-from-to A n

  RAL : Set → Set
  RAL A = RAL-g A 0

  -- TODO: implement all the operations on the datastructure:
  --   cf. "Numerical representation as higher-order nested datatypes", Fig. 3, p.13 for the interface
  --   cf. Okasaki, Sec. 9.2.1 and 10.1.2 for the implementation

  -- Returns an empty structure
  empty : ∀ {A} → RAL A
  empty = ϵ

  private
    -- Appends a new Tree in a structure of trees
    consTree : ∀ {A n} → Tree A n → RAL-g A n → RAL-g A n
    consTree l ϵ = ϵ [ l ]I
    consTree l (t O) = t [ l ]I
    consTree l (t [ l₁ ]I) = consTree (Node l l₁) t O

    -- Removes (and returns) the first tree of the list of trees if not empty
    unconsTree : ∀ {A n} → RAL-g A n → Maybe $ Tree A n × RAL-g A n
    unconsTree ϵ = nothing
    unconsTree (e O) with unconsTree e
    ... | just (Node t t₁ , ts) = just (t , ts [ t₁ ]I)
    ... | nothing = nothing
    unconsTree (e [ t ]I) = just (t , e O)

    -- Retrieves an element in a list of trees
    lookup-trees : ∀ {A n} → RAL-g A n → ℕ → Maybe A
    lookup-trees ϵ _ = nothing
    lookup-trees (r O) = lookup-trees r
    lookup-trees (_[_]I {k} s r) i = let pow = 2 ^ k in
      case i <? pow of λ {
        (yes p) → just $ lookup-tree r $ fromℕ< p ;
        (no _) → lookup-trees s (i ∸ pow)}

    -- Replaces an element inside the structure
    update-trees : ∀ {A n} → RAL-g A n → ℕ → A → RAL-g A n
    update-trees ϵ _ _ = ϵ
    update-trees (r O) i a = update-trees r i a O
    update-trees (_[_]I {k} r t) i a = let pow = 2 ^ k in
      case i <? pow of λ {
        (yes p) → r [ update-tree (fromℕ< p) a t ]I ;
        (no _) → (update-trees r (i ∸ pow)) a [ t ]I  }

  -- Appends an element at the beginning of the structure
  cons : ∀ {A} → A → RAL A → RAL A
  cons = consTree ∘ Leaf

  -- Returns the first element in the structure
  head : ∀ {A} → RAL A → Maybe A
  head r with unconsTree r
  ... | just (Leaf x , _) = just x
  ... | nothing = nothing

  -- Returns the smaller structure without its first element
  tail : ∀ {A} → RAL A → Maybe $ RAL A
  tail = Data.Maybe.map proj₂ ∘ unconsTree

  front : ∀ {A} → RAL A → A × RAL A
  front = {!!}

  snoc : ∀ {A} → RAL A → A → RAL A
  snoc = {!!}

  rear : ∀ {A} → RAL A → A × RAL A
  rear = {!!}

  access : ∀ {A} → RAL A → ℕ → Maybe A
  access = lookup-trees

  update : ∀ {A} → RAL A → ℕ → A → RAL A
  update = update-trees
