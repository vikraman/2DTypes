{-# OPTIONS --without-K #-} 

module 2D.Types where

infix 50 _⊕_
infix 60 _⊗_
infix 60 _//_
infix 60 _\\_
infix  30 _⟷_
infix  30 _⇔_
infixr 50 _◎_
infixr 70 _⊡_
infixr 60 _●_

-- The treatment of η and ε follows
-- https://en.wikipedia.org/wiki/Compact_closed_category

mutual
  data U : Set where
    𝟘 : U
    𝟙 : U
    _⊕_ : U → U → U
    _⊗_ : U → U → U
    # : {τ : U} → (τ ⟷ τ) → U
    _//_ : {τ : U} → (τ ⟷ τ) → (τ ⟷ τ) → U -- # c ⊗ 1/# d, tangled right
    _\\_ : {τ : U} → (τ ⟷ τ) → (τ ⟷ τ) → U -- 1/# d ⊗ # c, tangled left

  data Prim⟷ : U → U → Set where
    unite₊l :  {t : U} → Prim⟷ (𝟘 ⊕ t) t
    uniti₊l :  {t : U} → Prim⟷ t (𝟘 ⊕ t)
    unite₊r :  {t : U} → Prim⟷ (t ⊕ 𝟘) t
    uniti₊r :  {t : U} → Prim⟷ t (t ⊕ 𝟘)
    swap₊   :  {t₁ t₂ : U} → Prim⟷ (t₁ ⊕ t₂) (t₂ ⊕ t₁)
    assocl₊ :  {t₁ t₂ t₃ : U} → Prim⟷ (t₁ ⊕ (t₂ ⊕ t₃))  ((t₁ ⊕ t₂) ⊕ t₃)
    assocr₊ :  {t₁ t₂ t₃ : U} → Prim⟷ ((t₁ ⊕ t₂) ⊕ t₃) (t₁ ⊕ (t₂ ⊕ t₃))
    unite⋆l :  {t : U} → Prim⟷ (𝟙 ⊗ t) t
    uniti⋆l :  {t : U} → Prim⟷ t (𝟙 ⊗ t)
    unite⋆r :  {t : U} → Prim⟷ (t ⊗ 𝟙) t
    uniti⋆r :  {t : U} → Prim⟷ t (t ⊗ 𝟙)
    swap⋆   :  {t₁ t₂ : U} → Prim⟷ (t₁ ⊗ t₂) (t₂ ⊗ t₁)
    assocl⋆ :  {t₁ t₂ t₃ : U} → Prim⟷ (t₁ ⊗ (t₂ ⊗ t₃)) ((t₁ ⊗ t₂) ⊗ t₃)
    assocr⋆ :  {t₁ t₂ t₃ : U} → Prim⟷ ((t₁ ⊗ t₂) ⊗ t₃) (t₁ ⊗ (t₂ ⊗ t₃))
    absorbr :  {t : U} → Prim⟷ (𝟘 ⊗ t) 𝟘
    absorbl :  {t : U} → Prim⟷ (t ⊗ 𝟘) 𝟘
    factorzr :  {t : U} → Prim⟷ 𝟘 (t ⊗ 𝟘)
    factorzl :  {t : U} → Prim⟷ 𝟘 (𝟘 ⊗ t)
    dist :  {t₁ t₂ t₃ : U} → Prim⟷ ((t₁ ⊕ t₂) ⊗ t₃) ((t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃))
    factor :  {t₁ t₂ t₃ : U} → Prim⟷ ((t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃)) ((t₁ ⊕ t₂) ⊗ t₃)
    distl :  {t₁ t₂ t₃ : U} → Prim⟷ (t₁ ⊗ (t₂ ⊕ t₃)) ((t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃))
    factorl :  {t₁ t₂ t₃ : U} → Prim⟷ ((t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃)) (t₁ ⊗ (t₂ ⊕ t₃))
    id⟷ :  {t : U} → Prim⟷ t t

  data _⟷_ : U → U → Set where
    Prim : {t₁ t₂ : U} → (Prim⟷ t₁ t₂) → (t₁ ⟷ t₂)
    _◎_ :  {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
    _⊕_ :  {t₁ t₂ t₃ t₄ : U} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ⊕ t₂ ⟷ t₃ ⊕ t₄)
    _⊗_ :  {t₁ t₂ t₃ t₄ : U} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ⊗ t₂ ⟷ t₃ ⊗ t₄)
    -- ap⟷ : {t : U} {p : t ⟷ t} →  # p ⊗ t ⟷ # p ⊗ t
    -- ap⁻¹⟷ : {t : U} {p : t ⟷ t} →  # p ⊗ t ⟷ # p ⊗ t
    η- : {t : U} → (p : t ⟷ t) → 𝟙 ⟷ p \\ p
    η+ : {t : U} → (p : t ⟷ t) → 𝟙 ⟷ p // p
    ε+ : {t : U} → (p : t ⟷ t) → p // p ⟷ 𝟙
    ε- : {t : U} → (p : t ⟷ t) → p \\ p ⟷ 𝟙
    -- rather than assocl⋆, we need something to synchronize. Might need 2 more versions?
    synchr⋆ : {t : U} {p q : t ⟷ t} → (p // q) ⊗ # p ⟷ # p ⊗ (q \\ p)
    synchl⋆ : {t : U} {p q : t ⟷ t} → # p ⊗ (q \\ p) ⟷ (p // q) ⊗ # p
    -- we need to be able to do something to the numerator
--     app-num\\ : {t : U} {p q r : t ⟷ t} → (# p ⟷ # r) → q \\ p ⟷ q \\ r
--     app-num// : {t : U} {p q r : t ⟷ t} → (# p ⟷ # r) → p // q ⟷ r // q

-- convenient short hand
#1/ : {τ : U} → (τ ⟷ τ) → U
#1/ p = p // (Prim id⟷)

! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
! (Prim unite₊l)   = Prim uniti₊l
! (Prim uniti₊l)   = Prim unite₊l
! (Prim unite₊r)   = Prim uniti₊r
! (Prim uniti₊r)   = Prim unite₊r
! (Prim swap₊)     = Prim swap₊
! (Prim assocl₊)   = Prim assocr₊
! (Prim assocr₊)   = Prim assocl₊
! (Prim (unite⋆l {t}))   = Prim (uniti⋆l {t})
! (Prim (uniti⋆l {t}))   = Prim (unite⋆l {t})
! (Prim (unite⋆r {t}))   = Prim (uniti⋆r {t})
! (Prim (uniti⋆r {t}))   = Prim (unite⋆r {t})
! (Prim swap⋆)     = Prim swap⋆
! (Prim assocl⋆)   = Prim assocr⋆
! (Prim assocr⋆)   = Prim assocl⋆
! (Prim absorbl)   = Prim factorzr
! (Prim absorbr)   = Prim factorzl
! (Prim factorzl)  = Prim absorbr
! (Prim factorzr)  = Prim absorbl
! (Prim dist)      = Prim factor
! (Prim factor)    = Prim dist
! (Prim distl)     = Prim factorl
! (Prim factorl)   = Prim distl
! (Prim id⟷)       = Prim id⟷
! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁
! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
! (c₁ ⊗ c₂) = (! c₁) ⊗ (! c₂)
! (η- p)    = ε- p
! (η+ p)    = ε+ p
! (ε- p)    = η- p
! (ε+ p)    = η+ p
-- ! ap⟷ = ap⁻¹⟷ 
-- ! ap⁻¹⟷ = ap⟷
! synchr⋆ = synchl⋆
! synchl⋆ = synchr⋆
-- ! (app-num// f) = app-num// (! f) -- note how these are different
-- ! (app-num\\ f) = app-num\\ (! f)

data _⇔_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  assoc◎l : ∀ {t₁ t₂ t₃ t₄} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
    (c₁ ◎ (c₂ ◎ c₃)) ⇔ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : ∀ {t₁ t₂ t₃ t₄} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
    ((c₁ ◎ c₂) ◎ c₃) ⇔ (c₁ ◎ (c₂ ◎ c₃))
  idl◎l   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    (Prim id⟷ ◎ c) ⇔ c
  idl◎r   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    c ⇔ Prim id⟷ ◎ c
  idr◎l   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    (c ◎ Prim id⟷) ⇔ c
  idr◎r   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    c ⇔ (c ◎ Prim id⟷)
  id⇔     : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    c ⇔ c
  rinv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (! c ◎ c) ⇔ Prim id⟷
  rinv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → Prim id⟷ ⇔ (! c ◎ c)
  linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ ! c) ⇔ Prim id⟷
  linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → Prim id⟷ ⇔ (c ◎ ! c)
  _●_  : ∀ {t₁ t₂} {c₁ c₂ c₃ : t₁ ⟷ t₂} →
    (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊡_  : ∀ {t₁ t₂ t₃} {c₁ c₃ : t₁ ⟷ t₂} {c₂ c₄ : t₂ ⟷ t₃} →
    (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  resp⊗⇔  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊗ c₂) ⇔ (c₃ ⊗ c₄)
  hom⊕◎⇔ : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : U} {c₁ : τ₅ ⟷ τ₁} {c₂ : τ₆ ⟷ τ₂}
        {c₃ : τ₁ ⟷ τ₃} {c₄ : τ₂ ⟷ τ₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⇔ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⇔ : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : U} {c₁ : τ₅ ⟷ τ₁} {c₂ : τ₆ ⟷ τ₂}
        {c₃ : τ₁ ⟷ τ₃} {c₄ : τ₂ ⟷ τ₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⇔ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
  split⊕-id⟷ : {τ₁ τ₂ : U} → Prim (id⟷ {τ₁ ⊕ τ₂}) ⇔ Prim id⟷ ⊕ Prim id⟷
  id⟷⊕id⟷⇔ : {τ₁ τ₂ : U} → (Prim (id⟷ {τ₁}) ⊕ Prim (id⟷ {τ₂})) ⇔ Prim id⟷

{-  -- coherence for num-app
  resp-app-num// : {t : U} {p q r : t ⟷ t} → {c₀ c₁ : # p ⟷ # r} →
    c₀ ⇔ c₁ → app-num// {q = q} c₀ ⇔ app-num// c₁
  resp-app-num\\ : {t : U} {p q r : t ⟷ t} → {c₀ c₁ : # p ⟷ # r} →
    c₀ ⇔ c₁ → app-num\\ {q = q} c₀ ⇔ app-num\\ c₁
-}  
  -- coherence for compact closed categories
{-
  ccc₁l : {t : U} {p : t ⟷ t} → 
         uniti⋆r p ◎ (Prim id⟷ ⊗ η- p) ◎ Prim assocl⋆ ◎
         (ε+ p ⊗ Prim id⟷) ◎ unite⋆l p ⇔ (Prim id⟷)
  ccc₁r : {t : U} {p : t ⟷ t} →
         Prim id⟷ ⇔ uniti⋆r p ◎ (Prim id⟷ ⊗ η- p) ◎
         Prim assocl⋆ ◎ (ε+ p ⊗ Prim id⟷) ◎ unite⋆l# p 
  ccc₂l : {t : U} {p : t ⟷ t} →
         (((uniti⋆l# p ◎ (η+ p ⊗ Prim id⟷)) ◎ Prim assocr⋆) ◎
         (Prim id⟷ ⊗ ε- p)) ◎ unite⋆r# p ⇔ Prim id⟷
  ccc₂r : {t : U} {p : t ⟷ t} →
         Prim id⟷ ⇔ (((uniti⋆l# p ◎ (η+ p ⊗ Prim id⟷)) ◎
         Prim assocr⋆) ◎ (Prim id⟷ ⊗ ε- p)) ◎ unite⋆r# p
-}
  
2! : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
2! assoc◎l = assoc◎r
2! assoc◎r = assoc◎l
2! idl◎l = idl◎r
2! idl◎r = idl◎l
2! idr◎l = idr◎r
2! idr◎r = idr◎l
2! rinv◎l = rinv◎r
2! rinv◎r = rinv◎l
2! linv◎l = linv◎r
2! linv◎r = linv◎l
2! id⇔ = id⇔
2! (α ⊡ β) = (2! α) ⊡ (2! β)
2! (α ● β) = (2! β) ● (2! α)
2! (resp⊕⇔ α β) = resp⊕⇔ (2! α) (2! β)
2! (resp⊗⇔ α β) = resp⊗⇔ (2! α) (2! β)
2! hom⊕◎⇔ = hom◎⊕⇔
2! hom◎⊕⇔ = hom⊕◎⇔
2! split⊕-id⟷ = id⟷⊕id⟷⇔
2! id⟷⊕id⟷⇔ = split⊕-id⟷ 
-- 2! ccc₁l = ccc₁r
-- 2! ccc₁r = ccc₁l
-- 2! ccc₂l = ccc₂r
-- 2! ccc₂r = ccc₂l
-- 2! (resp-app-num// α) = resp-app-num// (2! α)
-- 2! (resp-app-num\\ α) = resp-app-num\\ (2! α)

-- Properties

!!⇔prim : {t₁ t₂ : U} → (p : Prim⟷ t₁ t₂) → Prim p ⇔ (! (! (Prim p)))
!!⇔prim unite₊l = id⇔
!!⇔prim uniti₊l = id⇔
!!⇔prim unite₊r = id⇔
!!⇔prim uniti₊r = id⇔
!!⇔prim swap₊ = id⇔
!!⇔prim assocl₊ = id⇔
!!⇔prim assocr₊ = id⇔
!!⇔prim unite⋆l = id⇔
!!⇔prim uniti⋆l = id⇔
!!⇔prim unite⋆r = id⇔
!!⇔prim uniti⋆r = id⇔
!!⇔prim swap⋆ = id⇔
!!⇔prim assocl⋆ = id⇔
!!⇔prim assocr⋆ = id⇔
!!⇔prim absorbr = id⇔
!!⇔prim absorbl = id⇔
!!⇔prim factorzr = id⇔
!!⇔prim factorzl = id⇔
!!⇔prim dist = id⇔
!!⇔prim factor = id⇔
!!⇔prim distl = id⇔
!!⇔prim factorl = id⇔
!!⇔prim id⟷ = id⇔

!!⇔id : {t₁ t₂ : U} → (p : t₁ ⟷ t₂) → p ⇔ ! (! p)
!!⇔id (_⟷_.Prim c) = !!⇔prim c
!!⇔id (p ◎ q) = !!⇔id p ⊡ !!⇔id q
!!⇔id (p _⟷_.⊕ q) = resp⊕⇔ (!!⇔id p) (!!⇔id q)
!!⇔id (p _⟷_.⊗ q) = resp⊗⇔ (!!⇔id p) (!!⇔id q)
!!⇔id (η+ p) = id⇔
!!⇔id (η- p) = id⇔
!!⇔id (ε+ p) = id⇔
!!⇔id (ε- p) = id⇔
-- !!⇔id ap⟷ = id⇔ 
-- !!⇔id ap⁻¹⟷ = id⇔
!!⇔id synchl⋆ = id⇔
!!⇔id synchr⋆ = id⇔
-- !!⇔id (app-num// f) = resp-app-num// (!!⇔id f)
-- !!⇔id (app-num\\ f) = resp-app-num\\ (!!⇔id f)

⇔! : {τ₁ τ₂ : U} {p q : τ₁ ⟷ τ₂} → (p ⇔ q) → (! p ⇔ ! q)
⇔! assoc◎l = assoc◎r
⇔! assoc◎r = assoc◎l
⇔! idl◎l = idr◎l
⇔! idl◎r = idr◎r
⇔! idr◎l = idl◎l
⇔! idr◎r = idl◎r
⇔! id⇔ = id⇔
⇔! rinv◎l = linv◎l
⇔! rinv◎r = linv◎r
⇔! linv◎l = rinv◎l
⇔! linv◎r = rinv◎r
⇔! (q₁ ● q₂) = (⇔! q₁) ● (⇔! q₂)
⇔! (q₁ ⊡ q₂) = ⇔! q₂ ⊡ ⇔! q₁
⇔! (resp⊕⇔ q₁ q₂) = resp⊕⇔ (⇔! q₁) (⇔! q₂)
⇔! (resp⊗⇔ q₁ q₂) = resp⊗⇔ (⇔! q₁) (⇔! q₂)
⇔! hom⊕◎⇔ = hom⊕◎⇔
⇔! hom◎⊕⇔ = hom◎⊕⇔
⇔! split⊕-id⟷ = split⊕-id⟷
⇔! id⟷⊕id⟷⇔ = id⟷⊕id⟷⇔
-- ⇔! ccc₁l = ccc₂l
-- ⇔! ccc₁r = ccc₂r
-- ⇔! ccc₂l = ccc₁l
-- ⇔! ccc₂r = ccc₁r
-- ⇔! (resp-app-num// α) = resp-app-num// (⇔! α)
-- ⇔! (resp-app-num\\ α) = resp-app-num\\ (⇔! α)

-- convenient lemmas

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

≡⇒⟷ : {τ₁ τ₂ : U} → τ₁ ≡ τ₂ → τ₁ ⟷ τ₂
≡⇒⟷ refl = Prim id⟷

≡⇒⇔ : {τ₁ τ₂ : U} {p q : τ₁ ⟷ τ₂} → p ≡ q → (p ⇔ q)
≡⇒⇔ refl = id⇔

inverse⇒⇔ : {τ₁ τ₂ : U} {p q : τ₁ ⟷ τ₂} → p ◎ ! q ⇔ Prim id⟷ → (p ⇔ q)
inverse⇒⇔ {p = p} {q} pf = idr◎r {c = p} ● (id⇔ ⊡ rinv◎r {c = q}) ● assoc◎l ● pf ⊡ id⇔ ● idl◎l

-- these patterns recur so often, let's name them
!aab⇔b : {s t u : U} {a : s ⟷ t} {b : t ⟷ u} → ! a ◎ a ◎ b ⇔ b
!aab⇔b = (assoc◎l ● rinv◎l ⊡ id⇔) ● idl◎l

ab!b⇔a : {s t u : U} {a : s ⟷ t} {b : t ⟷ u} → a ◎ b ◎ ! b ⇔ a
ab!b⇔a = id⇔ ⊡ linv◎l ● idr◎l

-----------------------
-- name : {t : U} {c d : t ⟷ t} (f : # c ⟷ # d) → (𝟙 ⟷ c \\ d)
-- name {_} {c} f = η- c ◎ app-num\\ f
-- 
-- coname : {t : U} {c d : t ⟷ t} (f : # c ⟷ # d) → (c // d ⟷ 𝟙)
-- coname {_} {c} {d} f = app-num// f ◎ ε+ d

--

open import Data.Product

open import Categories.Category
open import Categories.Groupoid
open import Categories.Groupoid.Sum
open import Level

El : U → Set₁
El t = Σ[ C ∈ Category zero zero zero ] (Groupoid C)

open import Universe

U-univ : Universe _ _
U-univ = record { U = U ; El = El }
