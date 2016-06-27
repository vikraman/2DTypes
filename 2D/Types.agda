module 2D.Types where

infix 50 _⊕_
infix 60 _⊗_
infix  30 _⟷_
infix  30 _⇔_
infixr 50 _◎_

-- The treatment of η and ε follows
-- https://en.wikipedia.org/wiki/Compact_closed_category

mutual
  data U : Set where
    𝟘 : U
    𝟙 : U
    _⊕_ : U → U → U
    _⊗_ : U → U → U
    # : {τ : U} → (τ ⟷ τ) → U
    1/# : {τ : U} → (τ ⟷ τ) → U

  data Prim⟷ : U → U → Set where
    unite₊l :  {t : U} → Prim⟷ (𝟘 ⊕ t) t
    uniti₊l :  {t : U} → Prim⟷ t (𝟘 ⊕ t)
    unite₊r :  {t : U} → Prim⟷ (t ⊕ 𝟘) t
    uniti₊r :  {t : U} → Prim⟷ t (t ⊕ 𝟘)
    swap₊   :  {t₁ t₂ : U} → Prim⟷ (t₁ ⊕ t₂) (t₂ ⊕ t₁)
    assocl₊ :  {t₁ t₂ t₃ : U} → Prim⟷ (t₁ ⊕ (t₂ ⊕ t₃))  ((t₁ ⊕ t₂) ⊕ t₃)
    assocr₊ :  {t₁ t₂ t₃ : U} → Prim⟷ ((t₁ ⊕ t₂) ⊕ t₃) (t₁ ⊕ (t₂ ⊕ t₃))
    unite⋆l :  {s t : U} → Prim⟷ (𝟙 ⊗ t) t
    uniti⋆l :  {s t : U} → Prim⟷ t (𝟙 ⊗ t)
    unite⋆r :  {s t : U} → Prim⟷ (t ⊗ 𝟙) t
    uniti⋆r :  {s t : U} → Prim⟷ t (t ⊗ 𝟙)
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
    foldSwap : {t : U} → (𝟙 ⊕ 𝟙) ⟷ (# (Prim (swap₊ {t} {t})))
    unfoldSwap : {t : U} → (# (Prim (swap₊ {t} {t}))) ⟷ (𝟙 ⊕ 𝟙) 
    ap⟷ : {t : U} {p : t ⟷ t} →  # p ⊗ t ⟷ # p ⊗ t
    ap⁻¹⟷ : {t : U} {p : t ⟷ t} →  # p ⊗ t ⟷ # p ⊗ t
    η- : {t : U} → (p : t ⟷ t) → # (Prim (id⟷ {t})) ⟷ (1/# p ⊗ # p)
    η+ : {t : U} → (p : t ⟷ t) → # (Prim (id⟷ {t})) ⟷ (# p ⊗ 1/# p)
    ε+ : {t : U} → (p : t ⟷ t) → (# p ⊗ 1/# p) ⟷ # (Prim (id⟷ {t}))
    ε- : {t : U} → (p : t ⟷ t) → (1/# p ⊗ # p) ⟷ # (Prim (id⟷ {t}))
    contract : {t : U} → # (Prim (id⟷ {t})) ⟷ 𝟙
    expand : {t : U} → 𝟙 ⟷ # (Prim (id⟷ {t}))
    iap⟷ : {t : U} {p : t ⟷ t} →  1/# p ⊗ t ⟷ 1/# p ⊗ t
    iap⁻¹⟷ : {t : U} {p : t ⟷ t} →  1/# p ⊗ t ⟷ 1/# p ⊗ t

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
! foldSwap = unfoldSwap
! unfoldSwap = foldSwap
! ap⟷ = ap⁻¹⟷ 
! ap⁻¹⟷ = ap⟷
! expand = contract
! contract = expand
! iap⟷ = iap⁻¹⟷ 
! iap⁻¹⟷ = iap⟷

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
  trans⇔  : ∀ {t₁ t₂} {c₁ c₂ c₃ : t₁ ⟷ t₂} →
    (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊡_  : ∀ {t₁ t₂ t₃} {c₁ c₃ : t₁ ⟷ t₂} {c₂ c₄ : t₂ ⟷ t₃} →
    (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  resp⊗⇔  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊗ c₂) ⇔ (c₃ ⊗ c₄)
  -- coherence for compact closed categories
  ccc₁l : {t : U} {p : t ⟷ t} →
         Prim (uniti⋆r {t}) ◎ (Prim id⟷ ⊗ expand) ◎ (Prim id⟷ ⊗ η- p) ◎ Prim assocl⋆ ◎
         (ε+ p ⊗ Prim id⟷) ◎ (contract ⊗ Prim id⟷) ◎ Prim (unite⋆l {t}) ⇔ Prim id⟷
  ccc₁r : {t : U} {p : t ⟷ t} →
         Prim id⟷ ⇔ Prim (uniti⋆r {t}) ◎ (Prim id⟷ ⊗ expand) ◎ (Prim id⟷ ⊗ η- p) ◎
         Prim assocl⋆ ◎ (ε+ p ⊗ Prim id⟷) ◎ (contract ⊗ Prim id⟷) ◎ Prim (unite⋆l {t})
  ccc₂l : {t : U} {p : t ⟷ t} →
         (((((Prim (uniti⋆l {t}) ◎ (expand ⊗ Prim id⟷)) ◎ (η+ p ⊗ Prim id⟷)) ◎ Prim assocr⋆) ◎
         (Prim id⟷ ⊗ ε- p)) ◎ (Prim id⟷ ⊗ contract)) ◎ Prim (unite⋆r {t}) ⇔ Prim id⟷
  ccc₂r : {t : U} {p : t ⟷ t} →
         Prim id⟷ ⇔ (((((Prim (uniti⋆l {t}) ◎ (expand ⊗ Prim id⟷)) ◎ (η+ p ⊗ Prim id⟷)) ◎
         Prim assocr⋆) ◎ (Prim id⟷ ⊗ ε- p)) ◎ (Prim id⟷ ⊗ contract)) ◎ Prim (unite⋆r {t})

  -- suggested alternate versions
  -- ccc₁l {t : U} {p : t ⟷ t} →
  --     uniti⋆r ◎ (id⟷ ⊗ η p) ◎ assocl⋆ ⇔ uniti⋆l ◎ ((η p ◎ swap⋆) ⊗ id⟷)
  
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
2! (trans⇔ α β) = trans⇔ (2! β) (2! α)
2! (resp⊕⇔ α β) = resp⊕⇔ (2! α) (2! β)
2! (resp⊗⇔ α β) = resp⊗⇔ (2! α) (2! β)
2! ccc₁l = ccc₁r
2! ccc₁r = ccc₁l
2! ccc₂l = ccc₂r
2! ccc₂r = ccc₂l

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
!!⇔id foldSwap = id⇔
!!⇔id unfoldSwap = id⇔
!!⇔id ap⟷ = id⇔ 
!!⇔id ap⁻¹⟷ = id⇔
!!⇔id contract = id⇔
!!⇔id expand = id⇔
!!⇔id iap⟷ = id⇔ 
!!⇔id iap⁻¹⟷ = id⇔ 

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
⇔! (trans⇔ q₁ q₂) = trans⇔ (⇔! q₁) (⇔! q₂)
⇔! (q₁ ⊡ q₂) = ⇔! q₂ ⊡ ⇔! q₁
⇔! (resp⊕⇔ q₁ q₂) = resp⊕⇔ (⇔! q₁) (⇔! q₂)
⇔! (resp⊗⇔ q₁ q₂) = resp⊗⇔ (⇔! q₁) (⇔! q₂)
⇔! ccc₁l = ccc₂l
⇔! ccc₁r = ccc₂r
⇔! ccc₂l = ccc₁l
⇔! ccc₂r = ccc₁r

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
