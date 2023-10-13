{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Vec
open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.HeterogeneousEquality hiding ([_])

open import Container.SkewBinary.CompleteBinaryTree
              renaming ( Tree to CTree
                       ; toVec to CTree-toVec
                       ; fromVec to CTree-fromVec)

-- Okasaki, Definition 9.3, p.118

module Container.Binary.Pennant where

data Tree (A : Set) : ℕ → Set where
  Leaf : A → Tree A 0
  Node : ∀ {n} → A → CTree A n → Tree A (suc n)

toVec : ∀ {A k} → Tree A k → Vec A (2 ^ k)
toVec (Leaf x) = [ x ]
toVec (Node a t) = {!!} -- a ∷ toVec t

fromVec : ∀ {A} k → Vec A (2 ^ k) → Tree A k
fromVec k vs = {!!}

iso-to-from : ∀ {A k} (t : Tree A k) → fromVec k (toVec t) ≡ t
iso-to-from = {!TO BE DONE!}

iso-from-to : ∀ {A} k (vs : Vec A (2 ^ k)) → toVec (fromVec k vs) ≡ vs
iso-from-to = {!TO BE DONE!}
