{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Base
import lib.types.Nat as N

open import Pi.Misc as N
open import Pi.Extra

module Pi.Syntax.SyntaxFull where

private
  variable
    m n o p q r : ℕ

-- Types

data U : Type₀ where
  O : U
  I : U
  _+_ : U → U → U
  _×_ : U → U → U

infixr 40 _+_ _×_
infix 30 _⟷₁_
infixr 50 _◎_ _⊕_

private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

-- 1-combinators

data _⟷₁_  : U → U → Type₀ where
  unite₊l : O + t ⟷₁  t
  uniti₊l : t ⟷₁  O + t
  unite⋆l : I × t ⟷₁  t
  uniti⋆l : t ⟷₁  I × t
  swap₊   : t₁ + t₂ ⟷₁  t₂ + t₁
  swap⋆   : t₁ × t₂ ⟷₁  t₂ × t₁
  assocl₊ : t₁ + (t₂ + t₃) ⟷₁  (t₁ + t₂) + t₃
  assocr₊ : (t₁ + t₂) + t₃ ⟷₁  t₁ + (t₂ + t₃)
  assocl⋆ : t₁ × (t₂ × t₃) ⟷₁  (t₁ × t₂) × t₃
  assocr⋆ : (t₁ × t₂) × t₃ ⟷₁  t₁ × (t₂ × t₃)
  absorbr : O × t ⟷₁  O
  absorbl : t × O ⟷₁  O
  factorzr : O ⟷₁  t × O
  factorzl : O ⟷₁  O × t
  dist : (t₁ + t₂) × t₃ ⟷₁  (t₁ × t₃) + (t₂ × t₃)
  distl : t₃ × (t₁ + t₂)  ⟷₁ (t₃ × t₁) + (t₃ × t₂)
  factor : {t₁ t₂ t₃ : U} → (t₁ × t₃) + (t₂ × t₃) ⟷₁ (t₁ + t₂) × t₃
  factorl : {t₁ t₂ t₃ : U} → (t₃ × t₁) + (t₃ ×  t₂) ⟷₁ t₃ × (t₁ + t₂)
  id⟷₁  : t ⟷₁  t
  _◎_     : (t₁ ⟷₁  t₂) → (t₂ ⟷₁  t₃) → (t₁ ⟷₁  t₃)
  _⊕_     : (t₁ ⟷₁  t₃) → (t₂ ⟷₁  t₄) → (t₁ + t₂ ⟷₁  t₃ + t₄)
  _⊗_     : (t₁ ⟷₁  t₃) → (t₂ ⟷₁  t₄) → (t₁ × t₂ ⟷₁  t₃ × t₄)

-- Equational reasoning

infixr 10 _⟷₁⟨_⟩_
infix  15 _⟷₁∎

_⟷₁⟨_⟩_ : (t₁ : U) → (t₁ ⟷₁  t₂) → (t₂ ⟷₁  t₃) → (t₁ ⟷₁  t₃)
_ ⟷₁⟨ c₁ ⟩ c₂ = c₁ ◎ c₂

_⟷₁∎ : (t : U) → t ⟷₁  t
_⟷₁∎ t = id⟷₁

-- Coherence

unite₊r : {t : U} → t + O ⟷₁  t
unite₊r = swap₊ ◎ unite₊l

uniti₊r : t ⟷₁  t + O
uniti₊r = uniti₊l ◎ swap₊

unite⋆r : {t : U} → t × I ⟷₁  t
unite⋆r = swap⋆ ◎ unite⋆l

uniti⋆r : t ⟷₁  t × I
uniti⋆r = uniti⋆l ◎ swap⋆

!⟷₁ : t₁ ⟷₁  t₂ → t₂ ⟷₁  t₁
!⟷₁ unite₊l = uniti₊l
!⟷₁ uniti₊l = unite₊l
!⟷₁ unite⋆l = uniti⋆l
!⟷₁ uniti⋆l = unite⋆l
!⟷₁ swap₊   = swap₊
!⟷₁ swap⋆   = swap⋆
!⟷₁ assocl₊ = assocr₊
!⟷₁ assocr₊ = assocl₊
!⟷₁ assocl⋆ = assocr⋆
!⟷₁ assocr⋆ = assocl⋆
!⟷₁ absorbr = factorzl
!⟷₁ absorbl = factorzr
!⟷₁ factorzr = absorbl
!⟷₁ factorzl = absorbr
!⟷₁ dist = factor
!⟷₁ distl = factorl
!⟷₁ factorl = distl
!⟷₁ factor = dist
!⟷₁ id⟷₁ = id⟷₁
!⟷₁ (c₁ ◎ c₂) = !⟷₁ c₂ ◎ !⟷₁ c₁
!⟷₁ (c₁ ⊕ c₂) = !⟷₁ c₁ ⊕ !⟷₁ c₂
!⟷₁ (c₁ ⊗ c₂) = !⟷₁ c₁ ⊗ !⟷₁ c₂


infix  30 _⟷₂_

data _⟷₂_ : {t₁ t₂ : U} → (t₁ ⟷₁ t₂) → (t₁ ⟷₁ t₂) → Set where
  assoc◎l : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₃ ⟷₁ t₄} →
          (c₁ ◎ (c₂ ◎ c₃)) ⟷₂ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₃ ⟷₁ t₄} →
          ((c₁ ◎ c₂) ◎ c₃) ⟷₂ (c₁ ◎ (c₂ ◎ c₃))
  assocl⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊) ⟷₂ (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃))
  assocl⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃)) ⟷₂ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊)
  assocl⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆) ⟷₂ (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃))
  assocl⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃)) ⟷₂ ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆)
  assocr⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⟷₂ (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃)))
  assocr⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
           (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃))) ⟷₂ (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆)
  assocr⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆) ⟷₂ (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃)))
  assocr⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
           (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))) ⟷₂ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
  dist⟷₂l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
      ((a ⊕ b) ⊗ c) ◎ dist ⟷₂ dist ◎ ((a ⊗ c) ⊕ (b ⊗ c))
  dist⟷₂r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
      dist ◎ ((a ⊗ c) ⊕ (b ⊗ c)) ⟷₂ ((a ⊕ b) ⊗ c) ◎ dist
  distl⟷₂l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
      (a ⊗ (b ⊕ c)) ◎ distl ⟷₂ distl ◎ ((a ⊗ b) ⊕ (a ⊗ c))
  distl⟷₂r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
      distl ◎ ((a ⊗ b) ⊕ (a ⊗ c)) ⟷₂ (a ⊗ (b ⊕ c)) ◎ distl
  factor⟷₂l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
       ((a ⊗ c) ⊕ (b ⊗ c)) ◎ factor ⟷₂ factor ◎ ((a ⊕ b) ⊗ c)
  factor⟷₂r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
       factor ◎ ((a ⊕ b) ⊗ c) ⟷₂ ((a ⊗ c) ⊕ (b ⊗ c)) ◎ factor
  factorl⟷₂l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
       ((a ⊗ b) ⊕ (a ⊗ c)) ◎ factorl ⟷₂ factorl ◎ (a ⊗ (b ⊕ c))
  factorl⟷₂r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
       factorl ◎ (a ⊗ (b ⊕ c)) ⟷₂ ((a ⊗ b) ⊕ (a ⊗ c)) ◎ factorl
  idl◎l   : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → (id⟷₁ ◎ c) ⟷₂ c
  idl◎r   : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → c ⟷₂ id⟷₁ ◎ c
  idr◎l   : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → (c ◎ id⟷₁) ⟷₂ c
  idr◎r   : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → c ⟷₂ (c ◎ id⟷₁)
  linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → (c ◎ !⟷₁ c) ⟷₂ id⟷₁
  linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → id⟷₁ ⟷₂ (c ◎ !⟷₁ c)
  rinv◎l  : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → (!⟷₁ c ◎ c) ⟷₂ id⟷₁
  rinv◎r  : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → id⟷₁ ⟷₂ (!⟷₁ c ◎ c)
  unite₊l⟷₂l : {t₁ t₂ : U} {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          (unite₊l ◎ c₂) ⟷₂ ((c₁ ⊕ c₂) ◎ unite₊l)
  unite₊l⟷₂r : {t₁ t₂ : U} {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          ((c₁ ⊕ c₂) ◎ unite₊l) ⟷₂ (unite₊l ◎ c₂)
  uniti₊l⟷₂l : {t₁ t₂ : U} {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          (uniti₊l ◎ (c₁ ⊕ c₂)) ⟷₂ (c₂ ◎ uniti₊l)
  uniti₊l⟷₂r : {t₁ t₂ : U} {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          (c₂ ◎ uniti₊l) ⟷₂ (uniti₊l ◎ (c₁ ⊕ c₂))
  unite₊r⟷₂l : {t₁ t₂ : U} {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          (unite₊r ◎ c₂) ⟷₂ ((c₂ ⊕ c₁) ◎ unite₊r)
  unite₊r⟷₂r : {t₁ t₂ : U} {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          ((c₂ ⊕ c₁) ◎ unite₊r) ⟷₂ (unite₊r ◎ c₂)
  uniti₊r⟷₂l : {t₁ t₂ : U} {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          (uniti₊r ◎ (c₂ ⊕ c₁)) ⟷₂ (c₂ ◎ uniti₊r)
  uniti₊r⟷₂r : {t₁ t₂ : U} {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          (c₂ ◎ uniti₊r) ⟷₂ (uniti₊r ◎ (c₂ ⊕ c₁))
  swapl₊⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} →
          (swap₊ ◎ (c₁ ⊕ c₂)) ⟷₂ ((c₂ ⊕ c₁) ◎ swap₊)
  swapr₊⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} →
          ((c₂ ⊕ c₁) ◎ swap₊) ⟷₂ (swap₊ ◎ (c₁ ⊕ c₂))
  unitel⋆⟷₂l : {t₁ t₂ : U} {c₁ : I ⟷₁ I} {c₂ : t₁ ⟷₁ t₂} →
          (unite⋆l ◎ c₂) ⟷₂ ((c₁ ⊗ c₂) ◎ unite⋆l)
  uniter⋆⟷₂l : {t₁ t₂ : U} {c₁ : I ⟷₁ I} {c₂ : t₁ ⟷₁ t₂} →
          ((c₁ ⊗ c₂) ◎ unite⋆l) ⟷₂ (unite⋆l ◎ c₂)
  unitil⋆⟷₂l : {t₁ t₂ : U} {c₁ : I ⟷₁ I} {c₂ : t₁ ⟷₁ t₂} →
          (uniti⋆l ◎ (c₁ ⊗ c₂)) ⟷₂ (c₂ ◎ uniti⋆l)
  unitir⋆⟷₂l : {t₁ t₂ : U} {c₁ : I ⟷₁ I} {c₂ : t₁ ⟷₁ t₂} →
          (c₂ ◎ uniti⋆l) ⟷₂ (uniti⋆l ◎ (c₁ ⊗ c₂))
  unitel⋆⟷₂r : {t₁ t₂ : U} {c₁ : I ⟷₁ I} {c₂ : t₁ ⟷₁ t₂} →
          (unite⋆r ◎ c₂) ⟷₂ ((c₂ ⊗ c₁) ◎ unite⋆r)
  uniter⋆⟷₂r : {t₁ t₂ : U} {c₁ : I ⟷₁ I} {c₂ : t₁ ⟷₁ t₂} →
          ((c₂ ⊗ c₁) ◎ unite⋆r) ⟷₂ (unite⋆r ◎ c₂)
  unitil⋆⟷₂r : {t₁ t₂ : U} {c₁ : I ⟷₁ I} {c₂ : t₁ ⟷₁ t₂} →
          (uniti⋆r ◎ (c₂ ⊗ c₁)) ⟷₂ (c₂ ◎ uniti⋆r)
  unitir⋆⟷₂r : {t₁ t₂ : U} {c₁ : I ⟷₁ I} {c₂ : t₁ ⟷₁ t₂} →
          (c₂ ◎ uniti⋆r) ⟷₂ (uniti⋆r ◎ (c₂ ⊗ c₁))
  swapl⋆⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} →
          (swap⋆ ◎ (c₁ ⊗ c₂)) ⟷₂ ((c₂ ⊗ c₁) ◎ swap⋆)
  swapr⋆⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} →
          ((c₂ ⊗ c₁) ◎ swap⋆) ⟷₂ (swap⋆ ◎ (c₁ ⊗ c₂))
  id⟷₂     : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → c ⟷₂ c
  trans⟷₂  : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷₁ t₂} →
         (c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₃) → (c₁ ⟷₂ c₃)
  _⊡_  : {t₁ t₂ t₃ : U}
         {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₁ ⟷₁ t₂} {c₄ : t₂ ⟷₁ t₃} →
         (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ◎ c₂) ⟷₂ (c₃ ◎ c₄)
  resp⊕⟷₂  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₁ ⟷₁ t₂} {c₄ : t₃ ⟷₁ t₄} →
         (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ⊕ c₂) ⟷₂ (c₃ ⊕ c₄)
  resp⊗⟷₂  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₁ ⟷₁ t₂} {c₄ : t₃ ⟷₁ t₄} →
         (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ⊗ c₂) ⟷₂ (c₃ ⊗ c₄)
--   -- below are the combinators added for the RigCategory structure
  id⟷⊕id⟷⟷₂ : {t₁ t₂ : U} → (id⟷₁ {t₁} ⊕ id⟷₁ {t₂}) ⟷₂ id⟷₁
  split⊕-id⟷ : {t₁ t₂ : U} → (id⟷₁ {_+_ t₁ t₂}) ⟷₂ (id⟷₁ ⊕ id⟷₁)
  hom⊕◎⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷₁ t₁} {c₂ : t₆ ⟷₁ t₂}
        {c₃ : t₁ ⟷₁ t₃} {c₄ : t₂ ⟷₁ t₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⟷₂ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷₁ t₁} {c₂ : t₆ ⟷₁ t₂}
        {c₃ : t₁ ⟷₁ t₃} {c₄ : t₂ ⟷₁ t₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⟷₂ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
  id⟷⊗id⟷⟷₂ : {t₁ t₂ : U} → (id⟷₁ {t₁} ⊗ id⟷₁ {t₂}) ⟷₂ id⟷₁
  split⊗-id⟷ : {t₁ t₂ : U} → (id⟷₁ {_×_ t₁ t₂}) ⟷₂ (id⟷₁ ⊗ id⟷₁)
  hom⊗◎⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷₁ t₁} {c₂ : t₆ ⟷₁ t₂}
        {c₃ : t₁ ⟷₁ t₃} {c₄ : t₂ ⟷₁ t₄} →
        ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄)) ⟷₂ ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄))
  hom◎⊗⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷₁ t₁} {c₂ : t₆ ⟷₁ t₂}
        {c₃ : t₁ ⟷₁ t₃} {c₄ : t₂ ⟷₁ t₄} →
         ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄)) ⟷₂ ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄))
--   -- associativity triangle
  triangle⊕l : {t₁ t₂ : U} →
    (unite₊r {t₁} ⊕ id⟷₁ {t₂}) ⟷₂ assocr₊ ◎ (id⟷₁ ⊕ unite₊l)
  triangle⊕r : {t₁ t₂ : U} →
    assocr₊ ◎ (id⟷₁ {t₁} ⊕ unite₊l {t₂}) ⟷₂ (unite₊r ⊕ id⟷₁)
  triangle⊗l : {t₁ t₂ : U} →
    ((unite⋆r {t₁}) ⊗ id⟷₁ {t₂}) ⟷₂ assocr⋆ ◎ (id⟷₁ ⊗ unite⋆l)
  triangle⊗r : {t₁ t₂ : U} →
    (assocr⋆ ◎ (id⟷₁ {t₁} ⊗ unite⋆l {t₂})) ⟷₂ (unite⋆r ⊗ id⟷₁)
  pentagon⊕l : {t₁ t₂ t₃ t₄ : U} →
    assocr₊ ◎ (assocr₊ {t₁} {t₂} {_+_ t₃ t₄}) ⟷₂
    ((assocr₊ ⊕ id⟷₁) ◎ assocr₊) ◎ (id⟷₁ ⊕ assocr₊)
  pentagon⊕r : {t₁ t₂ t₃ t₄ : U} →
    ((assocr₊ {t₁} {t₂} {t₃} ⊕ id⟷₁ {t₄}) ◎ assocr₊) ◎ (id⟷₁ ⊕ assocr₊) ⟷₂
    assocr₊ ◎ assocr₊
  pentagon⊗l : {t₁ t₂ t₃ t₄ : U} →
    assocr⋆ ◎ (assocr⋆ {t₁} {t₂} {_×_ t₃ t₄}) ⟷₂
    ((assocr⋆ ⊗ id⟷₁) ◎ assocr⋆) ◎ (id⟷₁ ⊗ assocr⋆)
  pentagon⊗r : {t₁ t₂ t₃ t₄ : U} →
    ((assocr⋆ {t₁} {t₂} {t₃} ⊗ id⟷₁ {t₄}) ◎ assocr⋆) ◎ (id⟷₁ ⊗ assocr⋆) ⟷₂
    assocr⋆ ◎ assocr⋆
--   -- from the braiding
--   -- unit coherence
  unite₊l-coh-l : {t₁ : U} → unite₊l {t₁} ⟷₂ swap₊ ◎ unite₊r
  unite₊l-coh-r : {t₁ : U} → swap₊ ◎ unite₊r ⟷₂ unite₊l {t₁}
  unite⋆l-coh-l : {t₁ : U} → unite⋆l {t₁} ⟷₂ swap⋆ ◎ unite⋆r
  unite⋆l-coh-r : {t₁ : U} → swap⋆ ◎ unite⋆r ⟷₂ unite⋆l {t₁}
  hexagonr⊕l : {t₁ t₂ t₃ : U} →
    (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃} ⟷₂
    ((swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ (id⟷₁ ⊕ swap₊)
  hexagonr⊕r : {t₁ t₂ t₃ : U} →
    ((swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ (id⟷₁ ⊕ swap₊) ⟷₂
    (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃}
  hexagonl⊕l : {t₁ t₂ t₃ : U} →
    (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃} ⟷₂
    ((id⟷₁ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷₁)
  hexagonl⊕r : {t₁ t₂ t₃ : U} →
    ((id⟷₁ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷₁) ⟷₂
    (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃}
  hexagonr⊗l : {t₁ t₂ t₃ : U} →
    (assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃} ⟷₂
    ((swap⋆ ⊗ id⟷₁) ◎ assocr⋆) ◎ (id⟷₁ ⊗ swap⋆)
  hexagonr⊗r : {t₁ t₂ t₃ : U} →
    ((swap⋆ ⊗ id⟷₁) ◎ assocr⋆) ◎ (id⟷₁ ⊗ swap⋆) ⟷₂
    (assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃}
  hexagonl⊗l : {t₁ t₂ t₃ : U} →
    (assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃} ⟷₂
    ((id⟷₁ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷₁)
  hexagonl⊗r : {t₁ t₂ t₃ : U} →
    ((id⟷₁ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷₁) ⟷₂
    (assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃}
  absorbl⟷₂l : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
    (c₁ ⊗ id⟷₁ {O}) ◎ absorbl ⟷₂ absorbl ◎ id⟷₁ {O}
  absorbl⟷₂r : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
    absorbl ◎ id⟷₁ {O} ⟷₂ (c₁ ⊗ id⟷₁ {O}) ◎ absorbl
  absorbr⟷₂l : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
    (id⟷₁ {O} ⊗ c₁) ◎ absorbr ⟷₂ absorbr ◎ id⟷₁ {O}
  absorbr⟷₂r : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
    absorbr ◎ id⟷₁ {O} ⟷₂ (id⟷₁ {O} ⊗ c₁) ◎ absorbr
  factorzl⟷₂l : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
    id⟷₁ ◎ factorzl ⟷₂ factorzl ◎ (id⟷₁ ⊗ c₁)
  factorzl⟷₂r : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
    factorzl ◎ (id⟷₁ {O} ⊗ c₁) ⟷₂ id⟷₁ {O} ◎ factorzl
  factorzr⟷₂l : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
    id⟷₁ ◎ factorzr ⟷₂ factorzr ◎ (c₁ ⊗ id⟷₁)
  factorzr⟷₂r : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
    factorzr ◎ (c₁ ⊗ id⟷₁) ⟷₂ id⟷₁ ◎ factorzr
  -- from the coherence conditions of RigCategory
  swap₊distl⟷₂l : {t₁ t₂ t₃ : U} →
    (id⟷₁ {t₁} ⊗ swap₊ {t₂} {t₃}) ◎ distl ⟷₂ distl ◎ swap₊
  swap₊distl⟷₂r : {t₁ t₂ t₃ : U} →
    distl ◎ swap₊ ⟷₂ (id⟷₁ {t₁} ⊗ swap₊ {t₂} {t₃}) ◎ distl
  dist-swap⋆⟷₂l : {t₁ t₂ t₃ : U} →
    dist {t₁} {t₂} {t₃} ◎ (swap⋆ ⊕ swap⋆) ⟷₂ swap⋆ ◎ distl
  dist-swap⋆⟷₂r : {t₁ t₂ t₃ : U} →
    swap⋆ ◎ distl {t₁} {t₂} {t₃} ⟷₂ dist ◎ (swap⋆ ⊕ swap⋆)
  assocl₊-dist-dist⟷₂l : {t₁ t₂ t₃ t₄ : U} →
    ((assocl₊ {t₁} {t₂} {t₃} ⊗ id⟷₁ {t₄}) ◎ dist) ◎ (dist ⊕ id⟷₁) ⟷₂
    (dist ◎ (id⟷₁ ⊕ dist)) ◎ assocl₊
  assocl₊-dist-dist⟷₂r : {t₁ t₂ t₃ t₄ : U} →
    (dist {t₁} ◎ (id⟷₁ ⊕ dist {t₂} {t₃} {t₄})) ◎ assocl₊ ⟷₂
    ((assocl₊ ⊗ id⟷₁) ◎ dist) ◎ (dist ⊕ id⟷₁)
  assocl⋆-distl⟷₂l : {t₁ t₂ t₃ t₄ : U} →
    assocl⋆ {t₁} {t₂} ◎ distl {_×_ t₁ t₂} {t₃} {t₄} ⟷₂
    ((id⟷₁ ⊗ distl) ◎ distl) ◎ (assocl⋆ ⊕ assocl⋆)
  assocl⋆-distl⟷₂r : {t₁ t₂ t₃ t₄ : U} →
    ((id⟷₁ ⊗ distl) ◎ distl) ◎ (assocl⋆ ⊕ assocl⋆) ⟷₂
    assocl⋆ {t₁} {t₂} ◎ distl {_×_ t₁ t₂} {t₃} {t₄}
  absorbr0-absorbl0⟷₂ : absorbr {O} ⟷₂ absorbl {O}
  absorbl0-absorbr0⟷₂ : absorbl {O} ⟷₂ absorbr {O}
  absorbr⟷₂distl-absorb-unite : {t₁ t₂ : U} →
    absorbr ⟷₂ (distl {t₁ = t₁} {t₂} ◎ (absorbr ⊕ absorbr)) ◎ unite₊l
  distl-absorb-unite⟷₂absorbr : {t₁ t₂ : U} →
    (distl {t₁ = t₁} {t₂} ◎ (absorbr ⊕ absorbr)) ◎ unite₊l ⟷₂ absorbr
  unite⋆r0-absorbr1⟷₂ : unite⋆r ⟷₂ absorbr
  absorbr1-unite⋆r-⟷₂ : absorbr ⟷₂ unite⋆r
  absorbl≡swap⋆◎absorbr : {t₁ : U} → absorbl {t₁} ⟷₂ swap⋆ ◎ absorbr
  swap⋆◎absorbr≡absorbl : {t₁ : U} → swap⋆ ◎ absorbr ⟷₂ absorbl {t₁}
  absorbr⟷₂[assocl⋆◎[absorbr⊗id⟷]]◎absorbr : {t₁ t₂ : U} →
    absorbr ⟷₂ (assocl⋆ {O} {t₁} {t₂} ◎ (absorbr ⊗ id⟷₁)) ◎ absorbr
  [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⟷₂absorbr : {t₁ t₂ : U} →
    (assocl⋆ {O} {t₁} {t₂} ◎ (absorbr ⊗ id⟷₁)) ◎ absorbr ⟷₂ absorbr
  [id⟷⊗absorbr]◎absorbl⟷₂assocl⋆◎[absorbl⊗id⟷]◎absorbr : {t₁ t₂ : U} →
    (id⟷₁ ⊗ absorbr {t₂}) ◎ absorbl {t₁} ⟷₂
    (assocl⋆ ◎ (absorbl ⊗ id⟷₁)) ◎ absorbr
  assocl⋆◎[absorbl⊗id⟷]◎absorbr⟷₂[id⟷⊗absorbr]◎absorbl : {t₁ t₂ : U} →
    (assocl⋆ ◎ (absorbl ⊗ id⟷₁)) ◎ absorbr ⟷₂
    (id⟷₁ ⊗ absorbr {t₂}) ◎ absorbl {t₁}
  elim⊥-A[0⊕B]⟷₂l : {t₁ t₂ : U} →
     (id⟷₁ {t₁} ⊗ unite₊l {t₂}) ⟷₂
     (distl ◎ (absorbl ⊕ id⟷₁)) ◎ unite₊l
  elim⊥-A[0⊕B]⟷₂r : {t₁ t₂ : U} →
     (distl ◎ (absorbl ⊕ id⟷₁)) ◎ unite₊l ⟷₂ (id⟷₁ {t₁} ⊗ unite₊l {t₂})
  elim⊥-1[A⊕B]⟷₂l : {t₁ t₂ : U} →
    unite⋆l ⟷₂
    distl ◎ (unite⋆l {t₁} ⊕ unite⋆l {t₂})
  elim⊥-1[A⊕B]⟷₂r : {t₁ t₂ : U} →
    distl ◎ (unite⋆l {t₁} ⊕ unite⋆l {t₂}) ⟷₂ unite⋆l
  fully-distribute⟷₂l : {t₁ t₂ t₃ t₄ : U} →
    (distl ◎ (dist {t₁} {t₂} {t₃} ⊕ dist {t₁} {t₂} {t₄})) ◎ assocl₊ ⟷₂
      ((((dist ◎ (distl ⊕ distl)) ◎ assocl₊) ◎ (assocr₊ ⊕ id⟷₁)) ◎
         ((id⟷₁ ⊕ swap₊) ⊕ id⟷₁)) ◎ (assocl₊ ⊕ id⟷₁)
  fully-distribute⟷₂r : {t₁ t₂ t₃ t₄ : U} →
    ((((dist ◎ (distl ⊕ distl)) ◎ assocl₊) ◎ (assocr₊ ⊕ id⟷₁)) ◎
       ((id⟷₁ ⊕ swap₊) ⊕ id⟷₁)) ◎ (assocl₊ ⊕ id⟷₁) ⟷₂
    (distl ◎ (dist {t₁} {t₂} {t₃} ⊕ dist {t₁} {t₂} {t₄})) ◎ assocl₊

data _⟷₃_ : {X Y : U} {p q : X ⟷₁ Y} → (p ⟷₂ q) → (p ⟷₂ q) → Set where
  trunc : {X Y : U} {p q : X ⟷₁ Y} (α β : p ⟷₂ q) → α ⟷₃ β

!!⟷₁ : (c : t₁ ⟷₁ t₂) → !⟷₁ (!⟷₁ c) ⟷₂ c
!!⟷₁ c = TODO!

!⟷₂ : {t₁ t₂ : U} → {c₁ c₂ : t₁ ⟷₁ t₂} → (α : c₁ ⟷₂ c₂) → c₂ ⟷₂ c₁
!⟷₂ α = TODO!