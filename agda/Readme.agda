{-# OPTIONS --rewriting #-}

-- 1. Numerical representations
-- 1.0 Generic
import Numerical.Generic.Dense
import Numerical.Generic.RunLength
-- 1.1 Base 1^k
import Numerical.Unary
-- 1.2 Base 2^k
import Numerical.Binary
-- 1.3 Base 2^{k+1}-1
import Numerical.SkewBinary

-- 2. Container
-- 2.1 Base 1^k
import Container.Unary.Singleton
-- 2.2 Base 2^k
import Container.Binary.BinomialHeap
import Container.Binary.LeafBinaryTree
-- 2.3 Base 2^{k+1}-1
import Container.SkewBinary.CompleteBinaryTree

-- 3. Structure
-- 3.0 Generic
import Structure.Generic.Dense
import Structure.Generic.RunLength
-- 3.1 Base 2^k
import Structure.Binary.Dense
import Structure.Binary.OneTwo

-- 4. Full-fledged data-structures
open import BinaryRandomAccessList
open import BinomialTree
open import OneTwoRandomAccessList
