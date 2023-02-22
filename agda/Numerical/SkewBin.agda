{-# OPTIONS --rewriting #-}

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Nat renaming (suc to sucℕ)
open import Relation.Binary.PropositionalEquality

open import Utils

{-# BUILTIN REWRITE _≡_ #-}


-- XXX: This file is now just a dump of unfinished thoughts. Everything else is in SkewBin/*.agda

module SkewBin where

  module Sparse where

    -- data View-ℕ : ℕ → Set where

    {-
    data Incr : Skew → Skew → Set where
      case-1 : Incr ϵ (ϵ I[ 0 ])                                                       -- 1. <- {0.}
      case-2 : ∀ {bs} → Incr (bs I[ 0 ]) (bs T[ 0 ])                                   -- 2. <- {1., 3.}
      case-3 : ∀ {bs c} → Incr (bs I[ sucℕ c ]) (bs I[ c ] I[ 0 ])                     -- 3. <- {4., 6.}
      case-4 : ∀ {c} → Incr (ϵ T[ c ]) (ϵ I[ sucℕ c ])                                 -- 4. <- {2., 5.}
      case-5 : ∀ {bs c} → Incr (bs I[ 0 ] T[ c ]) (bs T[ sucℕ c ])                     -- 5. <- {2., 5.}
      case-6 : ∀ {bs c₁ c₀} → Incr (bs I[ sucℕ c₁ ] T[ c₀ ]) (bs I[ c₁ ] I[ sucℕ c₀ ]) -- 6. <- {2., 5.}

    data Nat⇒Skew : ℕ → Skew → Set where
      case-0 : Nat⇒Skew 0 ϵ
      case-S : ∀ {n b Sb} → Nat⇒Skew n b → Incr b Sb → Nat⇒Skew (sucℕ n) Sb
    -}
    {-
    incr : Skew → Maybe Skew
    incr ϵ = just (ϵ I[ 0 ])                                        -- 1. <- {0.}
    incr (bs I[ 0 ]) = just (bs T[ 0 ])                             -- 2. <- {1., 3.}
    incr (bs I[ sucℕ c ]) = just (bs I[ c ] I[ 0 ])                 -- 3. <- {4., 6.}
    incr (ϵ T[ c ]) = just (ϵ I[ sucℕ c ])                          -- 4. <- {2., 5.}
    incr (bs I[ 0 ] T[ c ]) = just (bs T[ sucℕ c ])                 -- 5. <- {2., 5.}
    incr (bs I[ sucℕ c₁ ] T[ c₀ ]) = just (bs I[ c₁ ] I[ sucℕ c₀ ]) -- 6. <- {2., 5.}
    incr (bs T[ c₁ ] T[ c₀ ]) = nothing                             -- IMPOSSIBLE (how to be sure?)

    Nat⇒Skew : ℕ → Maybe Skew
    Nat⇒Skew zero = just ϵ
    Nat⇒Skew (sucℕ n) with Nat⇒Skew n
    ... | nothing = nothing
    ... | just k = incr k
    -}
    {-
    impossible : ∀ {bs}{c₁}{c₀}{b} {n} → Nat⇒Skew n b → ((b ≡  bs T[ c₁ ] T[ c₀ ]) → ⊥) × ((b ≡  bs T[ c₁ ] I[ c₀ ]) → ⊥)
    impossible case-0 = (λ { () }) , (λ { () })
    impossible (case-S p case-1) = ( (λ { () }) ) , ( (λ { () }) )
    impossible (case-S p case-2) =  {!!}
    impossible (case-S p case-3) = {!!}
    impossible (case-S p case-4) = {!!}
    impossible (case-S p case-5) = {!!}
    impossible (case-S p case-6) = {!!}
    -}

    {-
    data WF0 : Skew → Set
    data WF1 : Skew → Set
    data WF2 : Skew → Set
    data WF3 : Skew → Set
    data WF4 : Skew → Set
    data WF5 : Skew → Set
    data WF6 : Skew → Set

    data WF0 where
      wf0 : WF0 ϵ

    data WF1 where
      wf1<-0 : WF0 ϵ → WF1 (ϵ I[ 0 ])

    data WF2 where
      wf2<-1 : WF1 (ϵ I[ 0 ]) → WF2 (ϵ T[ 0 ])
      wf2<-3 : ∀ {bs c} → WF3 (bs I[ c ] I[ 0 ]) → WF2 {!!}
  
    data WF3 where
      wf3<-4 : ∀ {c} → WF4 (ϵ T[ c ]) → WF3 (ϵ I[ sucℕ c ])
      wf3<-6 : ∀ {b c₁ c₀} → WF6 (b I[ sucℕ c₁ ] T[ c₀ ]) → WF3 (b I[ c₁ ] I[ sucℕ c₀ ])

    data WF4 where

    data WF5 where
    
    data WF6 where

    data WF : Skew → Set where
      wf1 : ∀ {b} → WF1 b → WF b
      wf2 : ∀ {b} → WF2 b → WF b
      wf3 : ∀ {b} → WF3 b → WF b
      wf4 : ∀ {b} → WF4 b → WF b
      wf5 : ∀ {b} → WF5 b → WF b
      wf6 : ∀ {b} → WF6 b → WF b

    stab1 : ∀ {b} → WF0 b → ∃ λ b' → incr b ≡ just b' × WF1 b'
    stab1 wf0 = (ϵ I[ zero ]) , (refl , wf1<-0 wf0)

    stab2 : ∀ {b} → WF1 b ⊎ WF3 b → ∃ λ b' → incr b ≡ just b' × WF2 b'
    stab2 = {!!}

    stab3 : ∀ {b} → WF4 b ⊎ WF6 b → ∃ λ b' → incr b ≡ just b' × WF3 b'
    stab3 = {!!}

    stab456 : ∀ {b} → WF2 b ⊎ WF5 b → ∃ λ b' → incr b ≡ just b' × WF4 b' × WF5 b' × WF6 b'
    stab456 = {!!}

    sta : ∀ {b} → WF b → ∃ λ b' → incr b ≡ just b' × WF b'
    sta = {!!}

    -- Inv5 : Skew → Set
    -- Inv5 s = {!!}

    -- lemma-5 : ∀ bs c → Inv5 (bs I[ 0 ] T[ c ]) → ∃ λ b →  incr (bs I[ 0 ] T[ c ]) ≡ just b × Inv5 b
    -- lemma-5 bs c inv = {!!}

    {-
    rewrite-+0 : ∀ n → n + 0 ≡ n
    rewrite-+0 zero = refl
    rewrite-+0 (sucℕ n) rewrite rewrite-+0 n = refl

    rewrite-+S : ∀ n m → n + sucℕ m ≡ sucℕ (n + m)
    rewrite-+S zero m = refl
    rewrite-+S (sucℕ n) m rewrite rewrite-+S n m = refl
  
    {-# REWRITE rewrite-+0  #-}
    -}


    {-
    data Incr : Skew → Set where
      case-0 : Incr ϵ
      case-1 : Incr ϵ → Incr (ϵ I[ 0 ])
      case-2 : ∀ {bs} → Incr (bs I[ 0 ]) → Incr (bs T[ 0 ])
      case-3 : ∀ {bs}{c} → Incr (bs I[ sucℕ c ]) → Incr (bs I[ c ] I[ 0 ])
      case-4 : ∀ {c} → Incr (ϵ T[ c ]) → Incr (ϵ I[ sucℕ c ])
      case-5 : ∀ {bs}{c} → Incr (bs I[ 0 ] T[ c ]) → Incr (bs T[ sucℕ c ])
      case-6 : ∀ {bs}{c₁}{c₀} → Incr (bs I[ sucℕ c₁ ] T[ c₀ ]) → Incr (bs I[ c₁ ] I[ sucℕ c₀ ])

    len : ∀ {b} → Incr b → ℕ
    len case-0 = 0
    len (case-1 i) = sucℕ (len i)
    len (case-2 i) = sucℕ (len i)
    len (case-3 i) = sucℕ (len i)
    len (case-4 i) = sucℕ (len i)
    len (case-5 i) = sucℕ (len i)
    len (case-6 i) = sucℕ (len i)

    stab : ∀ {b} → (i : Incr b) → ∃ λ b' → incr b ≡ just b' × Incr b' × Skew⇒Nat b' ≡ sucℕ (len i)
    stab case-0 = ϵ I[ 0 ] , (refl , (case-1 case-0) , refl)
    stab (case-1 case-0) = (ϵ T[ zero ]) , (refl , (case-2 (case-1 case-0)) , refl)
    stab (case-2 {ϵ} (case-1 case-0)) = _ , (refl , (case-4 (case-2 (case-1 case-0)) , refl))
    stab (case-2 {bs I[ zero ]} t) = (bs T[ 1 ]) , (refl , ((case-5 (case-2 t)) , {!!}))
    stab (case-2 {bs I[ sucℕ x ]} t) = ((bs I[ x ]) I[ 1 ]) , (refl , ((case-6 (case-2  t)) , {!!}))
    stab (case-3 {c = zero} t) = ((_ I[ zero ]) T[ zero ]) , (refl , (case-2 (case-3 t) , {!!}))
    stab (case-3 {c = sucℕ c} t) = ((_ I[ sucℕ c ]) T[ zero ]) , (refl , (case-2 (case-3 t)) , {!!})
    stab (case-4 t) = ((ϵ I[ _ ]) I[ zero ]) , (refl , (case-3 (case-4 t) , {!!}))
    stab (case-5 {ϵ} t) = (ϵ I[ sucℕ (sucℕ _) ]) , (refl , ((case-4 (case-5 t)) , {!!}))
    stab (case-5 {bs I[ zero ]} t) = _ , (refl , ((case-5 (case-5 t)) , {!TRUE!}))
    stab (case-5 {bs I[ sucℕ x ]} t) = _ , (refl , ((case-6 (case-5 t)) , {!!}))
    stab (case-5 {ϵ T[ x ]} (case-2 (case-3 ())))
    stab (case-5 {ϵ T[ x ]} (case-5 (case-2 (case-3 (case-6 (case-2 (case-3 ())))))))
    stab (case-5 {ϵ T[ x ]} (case-5 (case-5 (case-2 (case-3 (case-6 (case-2 (case-3 (case-6 (case-5 (case-2 (case-3 (case-6 (case-2 t)))))))))))))) = {!!}
    stab (case-5 {ϵ T[ x ]} (case-5 (case-5 (case-5 t)))) = {!!}
    stab (case-5 {(bs I[ x₁ ]) T[ x ]} t) = {!!}
    stab (case-5 {(bs T[ x₁ ]) T[ x ]} t) = {!!}
    stab (case-6 t) = {!!}

    -- le : ∀ {b} → Incr b → Skew⇒Nat b ≡ 

    data View-incr : Skew → Set where
      case-1 : View-incr ϵ
      case-2 : ∀ bs → View-incr (bs I[ 0 ])
      case-3 : ∀ bs c → View-incr (bs I[ sucℕ c ])
      case-4 : ∀ c → View-incr (ϵ T[ c ])
      case-5 : ∀ bs c → View-incr (bs I[ 0 ] T[ c ])
      case-6 : ∀ bs c₁ c₀ → View-incr (bs I[ sucℕ c₁ ] T[ c₀ ])

    incr2 : ∀ bs → View-incr bs → Skew
    incr2 .ϵ case-1 = ϵ I[ 0 ]
    incr2 .(bs I[ 0 ]) (case-2 bs) = bs T[ 0 ]
    incr2 .(bs I[ sucℕ c ]) (case-3 bs c) = bs I[ c ] I[ 0 ]
    incr2 .(ϵ T[ c ]) (case-4 c) = ϵ I[ sucℕ c ]
    incr2 .((bs I[ 0 ]) T[ c ]) (case-5 bs c) = bs T[ sucℕ c ]
    incr2 .((bs I[ sucℕ c₁ ]) T[ c₀ ]) (case-6 bs c₁ c₀) = bs I[ c₁ ] I[ sucℕ c₀ ]

    -}
    {-
    ind : (b : Skew) → (P : Skew → Set) →
          P ϵ → (∀ b → P b → ∃ λ b' → incr b ≡ just b' × P b') → P b
    ind = {!!}

    correct-g : ∀ n → ∃ λ b → Nat⇒Skew n ≡ just b × WF b
    correct-g = {!!}

    specialize : ∀ {b} → WF b → Skew⇒Nat b ≡ {!!}
    specialize wf = {!!}

    correct : ∀ n → ∃ λ b → Nat⇒Skew n ≡ just b × Skew⇒Nat b ≡ n
    correct n with correct-g n
    ... | b , q , wf = b , (q , {!specialize wf!})

    correct2 : ∀ b' b → Nat⇒Skew (Skew⇒Nat b) ≡ just b' -> b ≡ b'
    correct2 = {!!}

    stable : (n : ℕ) → ∃ λ bs → View-incr bs × Skew⇒Nat bs ≡ n
    stable zero = ϵ , case-1 , refl
    stable (sucℕ n) with stable n
    ... | .ϵ , case-1 , refl = (ϵ I[ 0 ]) , ((case-2 ϵ) , refl)
    ... | .(ϵ I[ 0 ]) , case-2 ϵ , refl = (ϵ T[ 0 ]) , (case-4 zero , refl)
    ... | .((bs I[ x ]) I[ 0 ]) , case-2 (bs I[ x ]) , q = {!!}
    ... | .((bs T[ x ]) I[ 0 ]) , case-2 (bs T[ x ]) , q = {!!}
    ... | .(bs I[ sucℕ c ]) , case-3 bs c , q = {!!}
    ... | .(ϵ T[ c ]) , case-4 c , q = {!!}
    ... | .((bs I[ 0 ]) T[ c ]) , case-5 bs c , q = {!!}
    ... | .((bs I[ sucℕ c₁ ]) T[ c₀ ]) , case-6 bs c₁ c₀ , q = {!!}

    {-
    thm : ∀ n bs → just bs ≡ Nat⇒Skew n → ∃ λ bs' → incr bs ≡ just bs' × Skew⇒Nat bs' ≡ sucℕ n
    thm zero .ϵ refl = ϵ I[ 0 ] , refl , refl
    thm (sucℕ n) bs q = {!!}
    -}
    -}
    -- Bogus:
    lemma-2 : ∀ bs c n →
              (∃ λ c₀ → sucℕ c₀ ≡ c × Skew⇒Nat (bs I[ sucℕ c ]) ≡ n) →
              (∃ λ c₀ → sucℕ c₀ ≡ c × Skew⇒Nat (ϵ T[ c₀ ]) ≡ n) → 
              Skew⇒Nat (bs I[ c ]) ≡ sucℕ n
    lemma-2 bs zero n ih-3  ih-4 = {!!}
    lemma-2 ϵ (sucℕ c) .(Skew⇒Nat (ϵ T[ c ])) ih-3  (.c , refl , refl) = refl
    lemma-2 (bs I[ x ]) (sucℕ c) n ih-3 ih-4 = {!!}
    lemma-2 (bs T[ x ]) (sucℕ c) n ih-3 ih-4 = {!!}

    -- Useless:
    data incrT : Skew → ℕ → Set where
      case-5 : ∀ bs c → incrT (bs T[ sucℕ c ]) (sucℕ (Skew⇒Nat (bs I[ 0 ] T[ c ])))

    sound-incrT : ∀ bs n → incrT bs n → Skew⇒Nat bs ≡ n
    sound-incrT .(bs T[ sucℕ c ]) .(sucℕ (Skew⇒Nat ((bs I[ 0 ]) T[ c ]))) (case-5 bs c) = {!TRUE!}

    complete-incrT : ∀ bs c → incrT (bs T[ c ]) (Skew⇒Nat (bs T[ c ]))
    complete-incrT bs c = {!!}

    {-
    pf-valid : ∀ n → Skew⇒Nat (Nat⇒Skew n) ≡ n
    pf-valid zero = refl
    pf-valid (sucℕ zero) = refl
    pf-valid (sucℕ (sucℕ zero)) = refl
    pf-valid (sucℕ (sucℕ (sucℕ zero))) = refl
    pf-valid (sucℕ (sucℕ (sucℕ (sucℕ zero)))) = refl
    pf-valid (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ zero))))) = refl
    pf-valid (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ zero)))))) = refl
    pf-valid (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ zero))))))) = refl
    pf-valid (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ zero)))))))) = refl
    pf-valid (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ zero))))))))) = refl
    pf-valid (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ zero)))))))))) = refl
    pf-valid (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ zero))))))))))) = refl
    pf-valid (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ zero)))))))))))) = refl
    pf-valid (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ n))))))))))))) = {!!}

    data PSkew : Skew → Set where
      O : PSkew ϵ
      S : ∀{n} → PSkew n → PSkew (incr n)

    pSkew : (b : Skew) → PSkew b
    pSkew ϵ = O
    pSkew (b I[ x ]) = {!!}
    pSkew (b T[ x ]) = {!!}
  
    peano :  (P : Skew -> Set) ->
                  P ϵ ->
                ((b : Skew) -> P b -> P (incr b)) ->
                (b : Skew) -> P b
    peano P bz bs b = help b (pSkew b)
      where help : (b : Skew) → PSkew b → P b
            help .ϵ O = bz
            help .(incr n) (S {n} b) = bs n (help n b)
    -}
-- data Binary : Set where
--   one : Binary
--   0# : (bs : Binary) → Binary
--   1# : (bs : Binary) → Binary

-- ⟦_⟧Bin : Binary → ℕ
-- ⟦ one ⟧Bin = 1
-- ⟦ 0# bs ⟧Bin = 2 * ⟦ bs ⟧Bin
-- ⟦ 1# bs ⟧Bin = suc (2 * ⟦ bs ⟧Bin)

-- bOne : Binary 
-- bOne = one

-- bSuc : Binary → Binary
-- bSuc one = 0# one
-- bSuc (0# bs) = 1# bs
-- bSuc (1# bs) = 0# (bSuc bs)

-- data PBin : Binary → Set where
--   one : PBin bOne
--   suc : ∀{n} → PBin n → PBin (bSuc n)

-- twice : {b : Binary} → PBin b → PBin (0# b)
-- twice one = suc one
-- twice (suc n) = suc (suc (twice n))


-- pBin : (b : Binary) → PBin b
-- pBin one = one
-- pBin (0# bs) with pBin bs 
-- ... | t = twice t
-- pBin (1# bs) with pBin bs
-- ... | t = suc (twice t)


-- peanoBin :  (P : Binary -> Set) ->
--             (P bOne) ->
--             ((b : Binary) -> P b -> P (bSuc b)) ->
--             (b : Binary) -> P b
-- peanoBin P pone psuc b = help b (pBin b)
--   where help : (b : Binary) → PBin b → P b
--         help .one one = pone
--         help .(bSuc n) (suc {n} x) = psuc n (help n x)


    _ : Skew⇒Nat ϵ ≡ 0
    _ = refl

    _ : Skew⇒Nat (ϵ I[ 0 ]) ≡ 1
    _ = refl

    _ : Skew⇒Nat (ϵ T[ 0 ]) ≡ 2
    _ = refl

    _ : Skew⇒Nat (ϵ I[ 1 ]) ≡ 3
    _ = refl

    _ : Skew⇒Nat (ϵ I[ 0 ] I[ 0 ]) ≡ 4
    _ = refl

    _ : Skew⇒Nat (ϵ I[ 0 ] T[ 0 ]) ≡ 5
    _ = refl

    _ : Skew⇒Nat (ϵ T[ 1 ]) ≡ 6
    _ = refl

    _ : Skew⇒Nat (ϵ I[ 2 ]) ≡ 7
    _ = refl

    _ : Skew⇒Nat (ϵ I[ 3 ]) ≡ 15
    _ = refl

    _ : Skew⇒Nat (ϵ I[ 1 ] T[ 2 ]) ≡ 45
    _ = refl


  module SparseCanonical where

    data SkewI : Set where
      ϵ  : SkewI
      _I[_] : SkewI → ℕ → SkewI

    data SkewC : Set where
      ϵ  : SkewC
      _I[_] : SkewI → ℕ → SkewC
      _T[_] : SkewI → ℕ → SkewC

    SkewI⇒Nat : SkewI → ℕ → ℕ
    SkewI⇒Nat ϵ k = 0
    SkewI⇒Nat (bs I[ c ]) k = 
      {- 1 * -} 2^[ k + c +1]-1 
      + SkewI⇒Nat bs (1 + k + c)

    SkewC⇒Nat : SkewC → ℕ
    SkewC⇒Nat ϵ = 0
    SkewC⇒Nat (bs I[ c ]) = 
      {- 1 * -} 2^[ c +1]-1 
      + SkewI⇒Nat bs (1 + c)
    SkewC⇒Nat (bs T[ c ]) = 
      {- 2 * 2^[ k +1]-1 = -} 
         2^[ c +1]-1 + 2^[ c +1]-1 
      + SkewI⇒Nat bs (1 + c)

    Skew⇒Nat : SkewC → ℕ
    Skew⇒Nat = SkewC⇒Nat 

    _ : Skew⇒Nat ϵ ≡ 0
    _ = refl

    _ : Skew⇒Nat (ϵ I[ 0 ]) ≡ 1
    _ = refl

    _ : Skew⇒Nat (ϵ T[ 0 ]) ≡ 2
    _ = refl

    _ : Skew⇒Nat (ϵ I[ 1 ]) ≡ 3
    _ = refl

    _ : Skew⇒Nat (ϵ I[ 0 ] I[ 0 ]) ≡ 4
    _ = refl

    _ : Skew⇒Nat (ϵ I[ 0 ] T[ 0 ]) ≡ 5
    _ = refl

    _ : Skew⇒Nat (ϵ T[ 1 ]) ≡ 6
    _ = refl

    _ : Skew⇒Nat (ϵ I[ 2 ]) ≡ 7
    _ = refl

    _ : Skew⇒Nat (ϵ I[ 3 ]) ≡ 15
    _ = refl

    _ : Skew⇒Nat (ϵ I[ 1 ] T[ 2 ]) ≡ 45
    _ = refl

    incr : SkewC → SkewC
    incr ϵ = ϵ I[ 0 ] 
    incr (bs I[ 0 ]) = bs T[ 0 ]
    incr (bs I[ sucℕ c ]) = bs I[ c ] I[ 0 ]
    incr (bs T[ c ]) with bs 
    ... | ϵ = ϵ I[ sucℕ c ]
    ... | bs I[ zero ] = bs T[ sucℕ c ]
    ... | bs I[ sucℕ c₁ ] = bs I[ c₁ ] I[ sucℕ c ]

    pf-incr : ∀ s → 1 + (Skew⇒Nat s) ≡ Skew⇒Nat (incr s)
    pf-incr ϵ = refl
    pf-incr (bs I[ zero ]) = refl
    pf-incr (bs I[ sucℕ c ]) = refl
    pf-incr (ϵ T[ c ]) = refl
    pf-incr ((bs I[ zero ]) T[ c ]) = {!OK!}
    pf-incr ((bs I[ sucℕ x ]) T[ c ]) = {!OK!}
    -- Have:
    -- 2^[ c + sucℕ x +1]-1
    -- = 2^[ sucℕ (c + x) +1]-1
    -- = sucℕ (2^[ c + x +1]-1 + 2^[ c + x +1]-1)

    -- sucℕ
    -- (2^[ c +1]-1 + 
    --  2^[ c +1]-1 +
    -- sucℕ
    -- (2^[ c + sucℕ x +1]-1 + 
    --  2^[ c + sucℕ x +1]-1 +
    --  SkewI⇒Nat bs (sucℕ (sucℕ (c + sucℕ x)))))
    -- =
    -- sucℕ
    -- (2^[ c +1]-1 +
    --  2^[ c +1]-1 +
    --  sucℕ
    --  ((sucℕ
    --     (2^[ c + x +1]-1 + 2^[ c + x +1]-1)) +
    --   (sucℕ 
    --     (2^[ c + x +1]-1 + 2^[ c + x +1]-1)) +
    --   SkewI⇒Nat bs (sucℕ (sucℕ (sucℕ (c + x)))))))


    decr : SkewC → SkewC
    decr ϵ = ϵ
    decr (ϵ I[ sucℕ c ]) = ϵ T[ c ]
    decr ((bs I[ c₁ ]) I[ sucℕ c ]) = bs I[ sucℕ c₁ ]  T[ c ]
    decr (ϵ I[ zero ]) = ϵ
    decr ((bs I[ c ]) I[ zero ]) = bs I[ sucℕ c ]
    decr (bs T[ zero ]) = bs I[ zero ]
    decr (bs T[ sucℕ c ]) = bs I[ 0 ] T[ c ]

    pf-decr : ∀ s → pred (Skew⇒Nat s) ≡ Skew⇒Nat (decr s)
    pf-decr ϵ = refl
    pf-decr (ϵ I[ sucℕ c ]) = refl
    pf-decr ((bs I[ x ]) I[ sucℕ c ]) = {!OK!}
    pf-decr (ϵ I[ zero ]) = refl
    pf-decr ((bs I[ c ]) I[ zero ]) = refl
    pf-decr (x T[ zero ]) = refl
    pf-decr (x T[ sucℕ x₁ ]) = {!TRUE!}


  open Sparse

  RawSkew = Sparse.Skew

  _≅_ : RawSkew → RawSkew → Set
  s₁ ≅ s₂ = Sparse.Skew⇒Nat s₁ ≡ Sparse.Skew⇒Nat s₂

  rewr1 : ∀ {bs k c₂ c₁} → Sparse.Skew⇒Nat-g ((bs T[ c₂ ]) I[ c₁ ]) k ≡ {!Sparse.Skew⇒Nat-g (bs !}
  rewr1 = {!!}
-}
