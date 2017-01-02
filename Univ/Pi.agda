{-# OPTIONS --without-K #-}

module Univ.Pi where

infix  50 _⊕_
infix  60 _⊗_
infix  30 _⟷_
infix  30 _⇔_
infixr 50 _◎_
infixr 70 _⊡_
infixr 60 _●_

data 𝒰 : Set where
  𝟘 𝟙 : 𝒰
  _⊕_ _⊗_ : 𝒰 → 𝒰 → 𝒰

data _⟷_ : 𝒰 → 𝒰 → Set where
  unite₊l  : {t : 𝒰} → (𝟘 ⊕ t) ⟷ t
  uniti₊l  : {t : 𝒰} → t ⟷ (𝟘 ⊕ t)
  unite₊r  : {t : 𝒰} → (t ⊕ 𝟘) ⟷ t
  uniti₊r  : {t : 𝒰} → t ⟷ (t ⊕ 𝟘)
  swap₊    : {t₁ t₂ : 𝒰} → (t₁ ⊕ t₂) ⟷ (t₂ ⊕ t₁)
  assocl₊  : {t₁ t₂ t₃ : 𝒰} → (t₁ ⊕ (t₂ ⊕ t₃)) ⟷ ((t₁ ⊕ t₂) ⊕ t₃)
  assocr₊  : {t₁ t₂ t₃ : 𝒰} → ((t₁ ⊕ t₂) ⊕ t₃) ⟷ (t₁ ⊕ (t₂ ⊕ t₃))
  unite⋆l  : {t : 𝒰} → (𝟙 ⊗ t) ⟷ t
  uniti⋆l  : {t : 𝒰} → t ⟷ (𝟙 ⊗ t)
  unite⋆r  : {t : 𝒰} → (t ⊗ 𝟙) ⟷ t
  uniti⋆r  : {t : 𝒰} → t ⟷ (t ⊗ 𝟙)
  swap⋆    : {t₁ t₂ : 𝒰} → (t₁ ⊗ t₂) ⟷ (t₂ ⊗ t₁)
  assocl⋆  : {t₁ t₂ t₃ : 𝒰} → (t₁ ⊗ (t₂ ⊗ t₃)) ⟷ ((t₁ ⊗ t₂) ⊗ t₃)
  assocr⋆  : {t₁ t₂ t₃ : 𝒰} → ((t₁ ⊗ t₂) ⊗ t₃) ⟷ (t₁ ⊗ (t₂ ⊗ t₃))
  absorbr  : {t : 𝒰} → (𝟘 ⊗ t) ⟷ 𝟘
  absorbl  : {t : 𝒰} → (t ⊗ 𝟘) ⟷ 𝟘
  factorzr : {t : 𝒰} → 𝟘 ⟷ (t ⊗ 𝟘)
  factorzl : {t : 𝒰} → 𝟘 ⟷ (𝟘 ⊗ t)
  dist     : {t₁ t₂ t₃ : 𝒰} → ((t₁ ⊕ t₂) ⊗ t₃) ⟷ ((t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃))
  factor   : {t₁ t₂ t₃ : 𝒰} → ((t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃)) ⟷ ((t₁ ⊕ t₂) ⊗ t₃)
  distl    : {t₁ t₂ t₃ : 𝒰} → (t₁ ⊗ (t₂ ⊕ t₃)) ⟷ ((t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃))
  factorl  : {t₁ t₂ t₃ : 𝒰} → ((t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃)) ⟷ (t₁ ⊗ (t₂ ⊕ t₃))
  id⟷      : {t : 𝒰} → t ⟷ t
  _◎_      :  {t₁ t₂ t₃ : 𝒰} → (p : t₁ ⟷ t₂) → (q : t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_      :  {t₁ t₂ t₃ t₄ : 𝒰} → (p : t₁ ⟷ t₃) → (q : t₂ ⟷ t₄) → (t₁ ⊕ t₂ ⟷ t₃ ⊕ t₄)
  _⊗_      :  {t₁ t₂ t₃ t₄ : 𝒰} → (p : t₁ ⟷ t₃) → (q : t₂ ⟷ t₄) → (t₁ ⊗ t₂ ⟷ t₃ ⊗ t₄)

! : {t₁ t₂ : 𝒰} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
! unite₊l  = uniti₊l
! uniti₊l  = unite₊l
! unite₊r  = uniti₊r
! uniti₊r  = unite₊r
! swap₊    = swap₊
! assocl₊  = assocr₊
! assocr₊  = assocl₊
! unite⋆l  = uniti⋆l
! uniti⋆l  = unite⋆l
! unite⋆r  = uniti⋆r
! uniti⋆r  = unite⋆r
! swap⋆    = swap⋆
! assocl⋆  = assocr⋆
! assocr⋆  = assocl⋆
! absorbr  = factorzl
! absorbl  = factorzr
! factorzr = absorbl
! factorzl = absorbr
! dist     = factor
! factor   = dist
! distl    = factorl
! factorl  = distl
! id⟷      = id⟷
! (p ◎ q)  = ! q ◎ ! p
! (p ⊕ q)  = ! p ⊕ ! q
! (p ⊗ q)  = ! p ⊗ ! q

data _⇔_ : {t₁ t₂ : 𝒰} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
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
  rinv◎l  : {t₁ t₂ : 𝒰} {c : t₁ ⟷ t₂} → (! c ◎ c) ⇔ id⟷
  rinv◎r  : {t₁ t₂ : 𝒰} {c : t₁ ⟷ t₂} → id⟷ ⇔ (! c ◎ c)
  linv◎l  : {t₁ t₂ : 𝒰} {c : t₁ ⟷ t₂} → (c ◎ ! c) ⇔ id⟷
  linv◎r  : {t₁ t₂ : 𝒰} {c : t₁ ⟷ t₂} → id⟷ ⇔ (c ◎ ! c)
  _●_  : ∀ {t₁ t₂} {c₁ c₂ c₃ : t₁ ⟷ t₂} →
    (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊡_  : ∀ {t₁ t₂ t₃} {c₁ c₃ : t₁ ⟷ t₂} {c₂ c₄ : t₂ ⟷ t₃} →
    (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {t₁ t₂ t₃ t₄ : 𝒰}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  resp⊗⇔  : {t₁ t₂ t₃ t₄ : 𝒰}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊗ c₂) ⇔ (c₃ ⊗ c₄)
  hom⊕◎⇔ : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : 𝒰} {c₁ : τ₅ ⟷ τ₁} {c₂ : τ₆ ⟷ τ₂}
        {c₃ : τ₁ ⟷ τ₃} {c₄ : τ₂ ⟷ τ₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⇔ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⇔ : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : 𝒰} {c₁ : τ₅ ⟷ τ₁} {c₂ : τ₆ ⟷ τ₂}
        {c₃ : τ₁ ⟷ τ₃} {c₄ : τ₂ ⟷ τ₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⇔ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
  split⊕-id⟷ : {τ₁ τ₂ : 𝒰} → (id⟷ {τ₁ ⊕ τ₂}) ⇔ id⟷ ⊕ id⟷
  id⟷⊕id⟷⇔ : {τ₁ τ₂ : 𝒰} → ((id⟷ {τ₁}) ⊕ (id⟷ {τ₂})) ⇔ id⟷

2! : {t₁ t₂ : 𝒰} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
2! assoc◎l      = assoc◎r
2! assoc◎r      = assoc◎l
2! idl◎l        = idl◎r
2! idl◎r        = idl◎l
2! idr◎l        = idr◎r
2! idr◎r        = idr◎l
2! id⇔          = id⇔
2! rinv◎l       = rinv◎r
2! rinv◎r       = rinv◎l
2! linv◎l       = linv◎r
2! linv◎r       = linv◎l
2! (p ● q)      = 2! q ● 2! p
2! (p ⊡ q)      = 2! p ⊡ 2! q
2! (resp⊕⇔ p q) = resp⊕⇔ (2! p) (2! q)
2! (resp⊗⇔ p q) = resp⊗⇔ (2! p) (2! q)
2! hom⊕◎⇔       = hom◎⊕⇔
2! hom◎⊕⇔       = hom⊕◎⇔
2! split⊕-id⟷   = id⟷⊕id⟷⇔
2! id⟷⊕id⟷⇔     = split⊕-id⟷
