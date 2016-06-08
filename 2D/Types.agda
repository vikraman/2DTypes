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

  data _⟷_ : U → U → Set where
    unite₊l :  {t : U} → 𝟘 ⊕ t ⟷ t
    uniti₊l :  {t : U} → t ⟷ 𝟘 ⊕ t
    unite₊r :  {t : U} → t ⊕ 𝟘 ⟷ t
    uniti₊r :  {t : U} → t ⟷ t ⊕ 𝟘
    swap₊   :  {t₁ t₂ : U} → (t₁ ⊕ t₂) ⟷ (t₂ ⊕ t₁)
    assocl₊ :  {t₁ t₂ t₃ : U} → t₁ ⊕ (t₂ ⊕ t₃) ⟷ (t₁ ⊕ t₂) ⊕ t₃
    assocr₊ :  {t₁ t₂ t₃ : U} → (t₁ ⊕ t₂) ⊕ t₃ ⟷ t₁ ⊕ (t₂ ⊕ t₃)
    unite⋆l :  {t : U} → 𝟙 ⊗ t ⟷ t
    uniti⋆l :  {t : U} → t ⟷ 𝟙 ⊗ t
    unite⋆r :  {t : U} → t ⊗ 𝟙 ⟷ t
    uniti⋆r :  {t : U} → t ⟷ t ⊗ 𝟙
    swap⋆   :  {t₁ t₂ : U} → t₁ ⊗ t₂ ⟷ t₂ ⊗ t₁
    assocl⋆ :  {t₁ t₂ t₃ : U} → t₁ ⊗ (t₂ ⊗ t₃) ⟷ (t₁ ⊗ t₂) ⊗ t₃
    assocr⋆ :  {t₁ t₂ t₃ : U} → (t₁ ⊗ t₂) ⊗ t₃ ⟷ t₁ ⊗ (t₂ ⊗ t₃)
    absorbr :  {t : U} → 𝟘 ⊗ t ⟷ 𝟘
    absorbl :  {t : U} → t ⊗ 𝟘 ⟷ 𝟘
    factorzr :  {t : U} → 𝟘 ⟷ t ⊗ 𝟘
    factorzl :  {t : U} → 𝟘 ⟷ 𝟘 ⊗ t
    dist :  {t₁ t₂ t₃ : U} → (t₁ ⊕ t₂) ⊗ t₃ ⟷ (t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃)
    factor :  {t₁ t₂ t₃ : U} → (t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃) ⟷ (t₁ ⊕ t₂) ⊗ t₃
    distl :  {t₁ t₂ t₃ : U} → t₁ ⊗ (t₂ ⊕ t₃) ⟷ (t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃)
    factorl :  {t₁ t₂ t₃ : U} → (t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃) ⟷ t₁ ⊗ (t₂ ⊕ t₃)
    id⟷ :  {t : U} → t ⟷ t
    _◎_ :  {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
    _⊕_ :  {t₁ t₂ t₃ t₄ : U} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ⊕ t₂ ⟷ t₃ ⊕ t₄)
    _⊗_ :  {t₁ t₂ t₃ t₄ : U} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ⊗ t₂ ⟷ t₃ ⊗ t₄)
    η- : {t : U} → (p : t ⟷ t) → 𝟙 ⟷ (1/# p ⊗ # p)
    η+ : {t : U} → (p : t ⟷ t) → 𝟙 ⟷ (# p ⊗ 1/# p)
    ε+ : {t : U} → (p : t ⟷ t) → (# p ⊗ 1/# p) ⟷ 𝟙
    ε- : {t : U} → (p : t ⟷ t) → (1/# p ⊗ # p) ⟷ 𝟙

! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
! unite₊l   = uniti₊l
! uniti₊l   = unite₊l
! unite₊r   = uniti₊r
! uniti₊r   = unite₊r
! swap₊     = swap₊
! assocl₊   = assocr₊
! assocr₊   = assocl₊
! unite⋆l   = uniti⋆l
! uniti⋆l   = unite⋆l
! unite⋆r   = uniti⋆r
! uniti⋆r   = unite⋆r
! swap⋆     = swap⋆
! assocl⋆   = assocr⋆
! assocr⋆   = assocl⋆
! absorbl   = factorzr
! absorbr   = factorzl
! factorzl  = absorbr
! factorzr  = absorbl
! dist      = factor
! factor    = dist
! distl     = factorl
! factorl   = distl
! id⟷     = id⟷
! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁
! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
! (c₁ ⊗ c₂) = (! c₁) ⊗ (! c₂)
! (η- p)    = ε- p
! (η+ p)    = ε+ p
! (ε- p)    = η- p
! (ε+ p)    = η+ p

data _⇔_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  assoc◎l : ∀ {t₁ t₂ t₃ t₄} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
    (c₁ ◎ (c₂ ◎ c₃)) ⇔ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : ∀ {t₁ t₂ t₃ t₄} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
    ((c₁ ◎ c₂) ◎ c₃) ⇔ (c₁ ◎ (c₂ ◎ c₃))
  idl◎l   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    (id⟷ ◎ c) ⇔ c
  idl◎r   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    c ⇔ id⟷ ◎ c
  idr◎l   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    (c ◎ id⟷) ⇔ c
  idr◎r   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    c ⇔ (c ◎ id⟷)
  id⇔     : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    c ⇔ c
  rinv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (! c ◎ c) ⇔ id⟷
  rinv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (! c ◎ c)
  linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ ! c) ⇔ id⟷
  linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (c ◎ ! c)
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
         uniti⋆r ◎ (id⟷ ⊗ η- p) ◎ assocl⋆ ◎ (ε+ p ⊗ id⟷) ◎ unite⋆l ⇔ id⟷
  ccc₁r : {t : U} {p : t ⟷ t} →
         id⟷ ⇔ uniti⋆r ◎ (id⟷ ⊗ η- p) ◎ assocl⋆ ◎ (ε+ p ⊗ id⟷) ◎ unite⋆l 
  ccc₂l : {t : U} {p : t ⟷ t} →
         (((uniti⋆l ◎ (η+ p ⊗ id⟷)) ◎ assocr⋆) ◎ (id⟷ ⊗ ε- p)) ◎ unite⋆r ⇔ id⟷
  ccc₂r : {t : U} {p : t ⟷ t} →
         id⟷ ⇔ (((uniti⋆l ◎ (η+ p ⊗ id⟷)) ◎ assocr⋆) ◎ (id⟷ ⊗ ε- p)) ◎ unite⋆r

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
