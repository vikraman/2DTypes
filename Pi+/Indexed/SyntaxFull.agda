{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Base
import lib.types.Nat as N

open import Pi+.Misc as N
open import Pi+.Extra

module Pi+.Indexed.SyntaxFull where

private
  variable
    m n o p q r : ℕ

-- Types

-- FIXME: indexed version causes internal error

-- data U : ℕ → Type₀ where
--   O : U 0
--   I : U 1
--   _+_ : U m → U n → U (m N.+ n)
--   _×_ : U m → U n → U (m N.* n)

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
    -- t t₁ t₂ t₃ t₄ t₅ t₆ : U n
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
  factor : {t₁ t₂ t₃ : U} → (t₁ × t₃) + (t₂ × t₃) ⟷₁  (t₁ + t₂) × t₃
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
!⟷₁ factor = dist
!⟷₁ id⟷₁ = id⟷₁
!⟷₁ (c₁ ◎ c₂) = !⟷₁ c₂ ◎ !⟷₁ c₁
!⟷₁ (c₁ ⊕ c₂) = !⟷₁ c₁ ⊕ !⟷₁ c₂
!⟷₁ (c₁ ⊗ c₂) = !⟷₁ c₁ ⊗ !⟷₁ c₂

infix  30 _⟷₂_

data _⟷₂_ : {t₁ t₂ : U} → (t₁ ⟷₁ t₂) → (t₁ ⟷₁ t₂) → Set where
--   assoc◎l : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₃ ⟷₁ t₄} →
--           (c₁ ◎ (c₂ ◎ c₃)) ⟷₂ ((c₁ ◎ c₂) ◎ c₃)
--   assoc◎r : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₃ ⟷₁ t₄} →
--           ((c₁ ◎ c₂) ◎ c₃) ⟷₂ (c₁ ◎ (c₂ ◎ c₃))
--   assocl⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
--           ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊) ⟷₂ (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃))
--   assocl⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
--           (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃)) ⟷₂ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊)
--   assocl⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
--           ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆) ⟷₂ (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃))
--   assocl⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
--           (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃)) ⟷₂ ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆)
--   assocr⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
--           (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⟷₂ (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃)))
--   assocr⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
--            (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃))) ⟷₂ (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆)
--   assocr⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
--           (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆) ⟷₂ (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃)))
--   assocr⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
--            (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))) ⟷₂ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
--   dist⟷₂l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
--       ((a ⊕ b) ⊗ c) ◎ dist ⟷₂ dist ◎ ((a ⊗ c) ⊕ (b ⊗ c))
--   dist⟷₂r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
--       dist ◎ ((a ⊗ c) ⊕ (b ⊗ c)) ⟷₂ ((a ⊕ b) ⊗ c) ◎ dist
--   distl⟷₂l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
--       (a ⊗ (b ⊕ c)) ◎ distl ⟷₂ distl ◎ ((a ⊗ b) ⊕ (a ⊗ c))
--   distl⟷₂r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
--       distl ◎ ((a ⊗ b) ⊕ (a ⊗ c)) ⟷₂ (a ⊗ (b ⊕ c)) ◎ distl
--   factor⟷₂l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
--        ((a ⊗ c) ⊕ (b ⊗ c)) ◎ factor ⟷₂ factor ◎ ((a ⊕ b) ⊗ c)
--   factor⟷₂r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
--        factor ◎ ((a ⊕ b) ⊗ c) ⟷₂ ((a ⊗ c) ⊕ (b ⊗ c)) ◎ factor
--   factorl⟷₂l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
--        ((a ⊗ b) ⊕ (a ⊗ c)) ◎ factorl ⟷₂ factorl ◎ (a ⊗ (b ⊕ c))
--   factorl⟷₂r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
--           {a : t₁ ⟷₁ t₂} {b : t₃ ⟷₁ t₄} {c : t₅ ⟷₁ t₆} →
--        factorl ◎ (a ⊗ (b ⊕ c)) ⟷₂ ((a ⊗ b) ⊕ (a ⊗ c)) ◎ factorl
--   idl◎l   : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → (id⟷ ◎ c) ⟷₂ c
--   idl◎r   : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → c ⟷₂ id⟷ ◎ c
--   idr◎l   : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → (c ◎ id⟷) ⟷₂ c
--   idr◎r   : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → c ⟷₂ (c ◎ id⟷)
--   linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → (c ◎ ! c) ⟷₂ id⟷
--   linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → id⟷ ⟷₂ (c ◎ ! c)
--   rinv◎l  : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → (! c ◎ c) ⟷₂ id⟷
--   rinv◎r  : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → id⟷ ⟷₂ (! c ◎ c)
--   unite₊l⟷₂l : {t₁ t₂ : U} {c₁ : ZERO ⟷₁ ZERO} {c₂ : t₁ ⟷₁ t₂} →
--           (unite₊l ◎ c₂) ⟷₂ ((c₁ ⊕ c₂) ◎ unite₊l)
--   unite₊l⟷₂r : {t₁ t₂ : U} {c₁ : ZERO ⟷₁ ZERO} {c₂ : t₁ ⟷₁ t₂} →
--           ((c₁ ⊕ c₂) ◎ unite₊l) ⟷₂ (unite₊l ◎ c₂)
--   uniti₊l⟷₂l : {t₁ t₂ : U} {c₁ : ZERO ⟷₁ ZERO} {c₂ : t₁ ⟷₁ t₂} →
--           (uniti₊l ◎ (c₁ ⊕ c₂)) ⟷₂ (c₂ ◎ uniti₊l)
--   uniti₊l⟷₂r : {t₁ t₂ : U} {c₁ : ZERO ⟷₁ ZERO} {c₂ : t₁ ⟷₁ t₂} →
--           (c₂ ◎ uniti₊l) ⟷₂ (uniti₊l ◎ (c₁ ⊕ c₂))
--   unite₊r⟷₂l : {t₁ t₂ : U} {c₁ : ZERO ⟷₁ ZERO} {c₂ : t₁ ⟷₁ t₂} →
--           (unite₊r ◎ c₂) ⟷₂ ((c₂ ⊕ c₁) ◎ unite₊r)
--   unite₊r⟷₂r : {t₁ t₂ : U} {c₁ : ZERO ⟷₁ ZERO} {c₂ : t₁ ⟷₁ t₂} →
--           ((c₂ ⊕ c₁) ◎ unite₊r) ⟷₂ (unite₊r ◎ c₂)
--   uniti₊r⟷₂l : {t₁ t₂ : U} {c₁ : ZERO ⟷₁ ZERO} {c₂ : t₁ ⟷₁ t₂} →
--           (uniti₊r ◎ (c₂ ⊕ c₁)) ⟷₂ (c₂ ◎ uniti₊r)
--   uniti₊r⟷₂r : {t₁ t₂ : U} {c₁ : ZERO ⟷₁ ZERO} {c₂ : t₁ ⟷₁ t₂} →
--           (c₂ ◎ uniti₊r) ⟷₂ (uniti₊r ◎ (c₂ ⊕ c₁))
--   swapl₊⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} →
--           (swap₊ ◎ (c₁ ⊕ c₂)) ⟷₂ ((c₂ ⊕ c₁) ◎ swap₊)
--   swapr₊⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} →
--           ((c₂ ⊕ c₁) ◎ swap₊) ⟷₂ (swap₊ ◎ (c₁ ⊕ c₂))
--   unitel⋆⟷₂l : {t₁ t₂ : U} {c₁ : ONE ⟷₁ ONE} {c₂ : t₁ ⟷₁ t₂} →
--           (unite⋆l ◎ c₂) ⟷₂ ((c₁ ⊗ c₂) ◎ unite⋆l)
--   uniter⋆⟷₂l : {t₁ t₂ : U} {c₁ : ONE ⟷₁ ONE} {c₂ : t₁ ⟷₁ t₂} →
--           ((c₁ ⊗ c₂) ◎ unite⋆l) ⟷₂ (unite⋆l ◎ c₂)
--   unitil⋆⟷₂l : {t₁ t₂ : U} {c₁ : ONE ⟷₁ ONE} {c₂ : t₁ ⟷₁ t₂} →
--           (uniti⋆l ◎ (c₁ ⊗ c₂)) ⟷₂ (c₂ ◎ uniti⋆l)
--   unitir⋆⟷₂l : {t₁ t₂ : U} {c₁ : ONE ⟷₁ ONE} {c₂ : t₁ ⟷₁ t₂} →
--           (c₂ ◎ uniti⋆l) ⟷₂ (uniti⋆l ◎ (c₁ ⊗ c₂))
--   unitel⋆⟷₂r : {t₁ t₂ : U} {c₁ : ONE ⟷₁ ONE} {c₂ : t₁ ⟷₁ t₂} →
--           (unite⋆r ◎ c₂) ⟷₂ ((c₂ ⊗ c₁) ◎ unite⋆r)
--   uniter⋆⟷₂r : {t₁ t₂ : U} {c₁ : ONE ⟷₁ ONE} {c₂ : t₁ ⟷₁ t₂} →
--           ((c₂ ⊗ c₁) ◎ unite⋆r) ⟷₂ (unite⋆r ◎ c₂)
--   unitil⋆⟷₂r : {t₁ t₂ : U} {c₁ : ONE ⟷₁ ONE} {c₂ : t₁ ⟷₁ t₂} →
--           (uniti⋆r ◎ (c₂ ⊗ c₁)) ⟷₂ (c₂ ◎ uniti⋆r)
--   unitir⋆⟷₂r : {t₁ t₂ : U} {c₁ : ONE ⟷₁ ONE} {c₂ : t₁ ⟷₁ t₂} →
--           (c₂ ◎ uniti⋆r) ⟷₂ (uniti⋆r ◎ (c₂ ⊗ c₁))
--   swapl⋆⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} →
--           (swap⋆ ◎ (c₁ ⊗ c₂)) ⟷₂ ((c₂ ⊗ c₁) ◎ swap⋆)
--   swapr⋆⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} →
--           ((c₂ ⊗ c₁) ◎ swap⋆) ⟷₂ (swap⋆ ◎ (c₁ ⊗ c₂))
--   id⟷₂     : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → c ⟷₂ c
--   trans⟷₂  : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷₁ t₂} →
--          (c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₃) → (c₁ ⟷₂ c₃)
--   _⊡_  : {t₁ t₂ t₃ : U}
--          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₁ ⟷₁ t₂} {c₄ : t₂ ⟷₁ t₃} →
--          (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ◎ c₂) ⟷₂ (c₃ ◎ c₄)
--   resp⊕⟷₂  : {t₁ t₂ t₃ t₄ : U}
--          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₁ ⟷₁ t₂} {c₄ : t₃ ⟷₁ t₄} →
--          (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ⊕ c₂) ⟷₂ (c₃ ⊕ c₄)
--   resp⊗⟷₂  : {t₁ t₂ t₃ t₄ : U}
--          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₁ ⟷₁ t₂} {c₄ : t₃ ⟷₁ t₄} →
--          (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ⊗ c₂) ⟷₂ (c₃ ⊗ c₄)
--   -- below are the combinators added for the RigCategory structure
--   id⟷⊕id⟷⟷₂ : {t₁ t₂ : U} → (id⟷ {t₁} ⊕ id⟷ {t₂}) ⟷₂ id⟷
--   split⊕-id⟷ : {t₁ t₂ : U} → (id⟷ {PLUS t₁ t₂}) ⟷₂ (id⟷ ⊕ id⟷)
--   hom⊕◎⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷₁ t₁} {c₂ : t₆ ⟷₁ t₂}
--         {c₃ : t₁ ⟷₁ t₃} {c₄ : t₂ ⟷₁ t₄} →
--         ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⟷₂ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
--   hom◎⊕⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷₁ t₁} {c₂ : t₆ ⟷₁ t₂}
--         {c₃ : t₁ ⟷₁ t₃} {c₄ : t₂ ⟷₁ t₄} →
--          ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⟷₂ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
--   id⟷⊗id⟷⟷₂ : {t₁ t₂ : U} → (id⟷ {t₁} ⊗ id⟷ {t₂}) ⟷₂ id⟷
--   split⊗-id⟷ : {t₁ t₂ : U} → (id⟷ {TIMES t₁ t₂}) ⟷₂ (id⟷ ⊗ id⟷)
--   hom⊗◎⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷₁ t₁} {c₂ : t₆ ⟷₁ t₂}
--         {c₃ : t₁ ⟷₁ t₃} {c₄ : t₂ ⟷₁ t₄} →
--         ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄)) ⟷₂ ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄))
--   hom◎⊗⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷₁ t₁} {c₂ : t₆ ⟷₁ t₂}
--         {c₃ : t₁ ⟷₁ t₃} {c₄ : t₂ ⟷₁ t₄} →
--          ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄)) ⟷₂ ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄))
--   -- associativity triangle
--   triangle⊕l : {t₁ t₂ : U} →
--     (unite₊r {t₁} ⊕ id⟷ {t₂}) ⟷₂ assocr₊ ◎ (id⟷ ⊕ unite₊l)
--   triangle⊕r : {t₁ t₂ : U} →
--     assocr₊ ◎ (id⟷ {t₁} ⊕ unite₊l {t₂}) ⟷₂ (unite₊r ⊕ id⟷)
--   triangle⊗l : {t₁ t₂ : U} →
--     ((unite⋆r {t₁}) ⊗ id⟷ {t₂}) ⟷₂ assocr⋆ ◎ (id⟷ ⊗ unite⋆l)
--   triangle⊗r : {t₁ t₂ : U} →
--     (assocr⋆ ◎ (id⟷ {t₁} ⊗ unite⋆l {t₂})) ⟷₂ (unite⋆r ⊗ id⟷)
--   pentagon⊕l : {t₁ t₂ t₃ t₄ : U} →
--     assocr₊ ◎ (assocr₊ {t₁} {t₂} {PLUS t₃ t₄}) ⟷₂
--     ((assocr₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊)
--   pentagon⊕r : {t₁ t₂ t₃ t₄ : U} →
--     ((assocr₊ {t₁} {t₂} {t₃} ⊕ id⟷ {t₄}) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊) ⟷₂
--     assocr₊ ◎ assocr₊
--   pentagon⊗l : {t₁ t₂ t₃ t₄ : U} →
--     assocr⋆ ◎ (assocr⋆ {t₁} {t₂} {TIMES t₃ t₄}) ⟷₂
--     ((assocr⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆)
--   pentagon⊗r : {t₁ t₂ t₃ t₄ : U} →
--     ((assocr⋆ {t₁} {t₂} {t₃} ⊗ id⟷ {t₄}) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆) ⟷₂
--     assocr⋆ ◎ assocr⋆
--   -- from the braiding
--   -- unit coherence
--   unite₊l-coh-l : {t₁ : U} → unite₊l {t₁} ⟷₂ swap₊ ◎ unite₊r
--   unite₊l-coh-r : {t₁ : U} → swap₊ ◎ unite₊r ⟷₂ unite₊l {t₁}
--   unite⋆l-coh-l : {t₁ : U} → unite⋆l {t₁} ⟷₂ swap⋆ ◎ unite⋆r
--   unite⋆l-coh-r : {t₁ : U} → swap⋆ ◎ unite⋆r ⟷₂ unite⋆l {t₁}
--   hexagonr⊕l : {t₁ t₂ t₃ : U} →
--     (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃} ⟷₂
--     ((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊)
--   hexagonr⊕r : {t₁ t₂ t₃ : U} →
--     ((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊) ⟷₂
--     (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃}
--   hexagonl⊕l : {t₁ t₂ t₃ : U} →
--     (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃} ⟷₂
--     ((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷)
--   hexagonl⊕r : {t₁ t₂ t₃ : U} →
--     ((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷) ⟷₂
--     (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃}
--   hexagonr⊗l : {t₁ t₂ t₃ : U} →
--     (assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃} ⟷₂
--     ((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆)
--   hexagonr⊗r : {t₁ t₂ t₃ : U} →
--     ((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆) ⟷₂
--     (assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃}
--   hexagonl⊗l : {t₁ t₂ t₃ : U} →
--     (assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃} ⟷₂
--     ((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷)
--   hexagonl⊗r : {t₁ t₂ t₃ : U} →
--     ((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷) ⟷₂
--     (assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃}
--   absorbl⟷₂l : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
--     (c₁ ⊗ id⟷ {ZERO}) ◎ absorbl ⟷₂ absorbl ◎ id⟷ {ZERO}
--   absorbl⟷₂r : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
--     absorbl ◎ id⟷ {ZERO} ⟷₂ (c₁ ⊗ id⟷ {ZERO}) ◎ absorbl
--   absorbr⟷₂l : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
--     (id⟷ {ZERO} ⊗ c₁) ◎ absorbr ⟷₂ absorbr ◎ id⟷ {ZERO}
--   absorbr⟷₂r : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
--     absorbr ◎ id⟷ {ZERO} ⟷₂ (id⟷ {ZERO} ⊗ c₁) ◎ absorbr
--   factorzl⟷₂l : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
--     id⟷ ◎ factorzl ⟷₂ factorzl ◎ (id⟷ ⊗ c₁)
--   factorzl⟷₂r : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
--     factorzl ◎ (id⟷ {ZERO} ⊗ c₁) ⟷₂ id⟷ {ZERO} ◎ factorzl
--   factorzr⟷₂l : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
--     id⟷ ◎ factorzr ⟷₂ factorzr ◎ (c₁ ⊗ id⟷)
--   factorzr⟷₂r : {t₁ t₂ : U} {c₁ : t₁ ⟷₁ t₂} →
--     factorzr ◎ (c₁ ⊗ id⟷) ⟷₂ id⟷ ◎ factorzr
--   -- from the coherence conditions of RigCategory
--   swap₊distl⟷₂l : {t₁ t₂ t₃ : U} →
--     (id⟷ {t₁} ⊗ swap₊ {t₂} {t₃}) ◎ distl ⟷₂ distl ◎ swap₊
--   swap₊distl⟷₂r : {t₁ t₂ t₃ : U} →
--     distl ◎ swap₊ ⟷₂ (id⟷ {t₁} ⊗ swap₊ {t₂} {t₃}) ◎ distl
--   dist-swap⋆⟷₂l : {t₁ t₂ t₃ : U} →
--     dist {t₁} {t₂} {t₃} ◎ (swap⋆ ⊕ swap⋆) ⟷₂ swap⋆ ◎ distl
--   dist-swap⋆⟷₂r : {t₁ t₂ t₃ : U} →
--     swap⋆ ◎ distl {t₁} {t₂} {t₃} ⟷₂ dist ◎ (swap⋆ ⊕ swap⋆)
--   assocl₊-dist-dist⟷₂l : {t₁ t₂ t₃ t₄ : U} →
--     ((assocl₊ {t₁} {t₂} {t₃} ⊗ id⟷ {t₄}) ◎ dist) ◎ (dist ⊕ id⟷) ⟷₂
--     (dist ◎ (id⟷ ⊕ dist)) ◎ assocl₊
--   assocl₊-dist-dist⟷₂r : {t₁ t₂ t₃ t₄ : U} →
--     (dist {t₁} ◎ (id⟷ ⊕ dist {t₂} {t₃} {t₄})) ◎ assocl₊ ⟷₂
--     ((assocl₊ ⊗ id⟷) ◎ dist) ◎ (dist ⊕ id⟷)
--   assocl⋆-distl⟷₂l : {t₁ t₂ t₃ t₄ : U} →
--     assocl⋆ {t₁} {t₂} ◎ distl {TIMES t₁ t₂} {t₃} {t₄} ⟷₂
--     ((id⟷ ⊗ distl) ◎ distl) ◎ (assocl⋆ ⊕ assocl⋆)
--   assocl⋆-distl⟷₂r : {t₁ t₂ t₃ t₄ : U} →
--     ((id⟷ ⊗ distl) ◎ distl) ◎ (assocl⋆ ⊕ assocl⋆) ⟷₂
--     assocl⋆ {t₁} {t₂} ◎ distl {TIMES t₁ t₂} {t₃} {t₄}
--   absorbr0-absorbl0⟷₂ : absorbr {ZERO} ⟷₂ absorbl {ZERO}
--   absorbl0-absorbr0⟷₂ : absorbl {ZERO} ⟷₂ absorbr {ZERO}
--   absorbr⟷₂distl-absorb-unite : {t₁ t₂ : U} →
--     absorbr ⟷₂ (distl {t₂ = t₁} {t₂} ◎ (absorbr ⊕ absorbr)) ◎ unite₊l
--   distl-absorb-unite⟷₂absorbr : {t₁ t₂ : U} →
--     (distl {t₂ = t₁} {t₂} ◎ (absorbr ⊕ absorbr)) ◎ unite₊l ⟷₂ absorbr
--   unite⋆r0-absorbr1⟷₂ : unite⋆r ⟷₂ absorbr
--   absorbr1-unite⋆r-⟷₂ : absorbr ⟷₂ unite⋆r
--   absorbl≡swap⋆◎absorbr : {t₁ : U} → absorbl {t₁} ⟷₂ swap⋆ ◎ absorbr
--   swap⋆◎absorbr≡absorbl : {t₁ : U} → swap⋆ ◎ absorbr ⟷₂ absorbl {t₁}
--   absorbr⟷₂[assocl⋆◎[absorbr⊗id⟷]]◎absorbr : {t₁ t₂ : U} →
--     absorbr ⟷₂ (assocl⋆ {ZERO} {t₁} {t₂} ◎ (absorbr ⊗ id⟷)) ◎ absorbr
--   [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⟷₂absorbr : {t₁ t₂ : U} →
--     (assocl⋆ {ZERO} {t₁} {t₂} ◎ (absorbr ⊗ id⟷)) ◎ absorbr ⟷₂ absorbr
--   [id⟷⊗absorbr]◎absorbl⟷₂assocl⋆◎[absorbl⊗id⟷]◎absorbr : {t₁ t₂ : U} →
--     (id⟷ ⊗ absorbr {t₂}) ◎ absorbl {t₁} ⟷₂
--     (assocl⋆ ◎ (absorbl ⊗ id⟷)) ◎ absorbr
--   assocl⋆◎[absorbl⊗id⟷]◎absorbr⟷₂[id⟷⊗absorbr]◎absorbl : {t₁ t₂ : U} →
--     (assocl⋆ ◎ (absorbl ⊗ id⟷)) ◎ absorbr ⟷₂
--     (id⟷ ⊗ absorbr {t₂}) ◎ absorbl {t₁}
--   elim⊥-A[0⊕B]⟷₂l : {t₁ t₂ : U} →
--      (id⟷ {t₁} ⊗ unite₊l {t₂}) ⟷₂
--      (distl ◎ (absorbl ⊕ id⟷)) ◎ unite₊l
--   elim⊥-A[0⊕B]⟷₂r : {t₁ t₂ : U} →
--      (distl ◎ (absorbl ⊕ id⟷)) ◎ unite₊l ⟷₂ (id⟷ {t₁} ⊗ unite₊l {t₂})
--   elim⊥-1[A⊕B]⟷₂l : {t₁ t₂ : U} →
--     unite⋆l ⟷₂
--     distl ◎ (unite⋆l {t₁} ⊕ unite⋆l {t₂})
--   elim⊥-1[A⊕B]⟷₂r : {t₁ t₂ : U} →
--     distl ◎ (unite⋆l {t₁} ⊕ unite⋆l {t₂}) ⟷₂ unite⋆l
--   fully-distribute⟷₂l : {t₁ t₂ t₃ t₄ : U} →
--     (distl ◎ (dist {t₁} {t₂} {t₃} ⊕ dist {t₁} {t₂} {t₄})) ◎ assocl₊ ⟷₂
--       ((((dist ◎ (distl ⊕ distl)) ◎ assocl₊) ◎ (assocr₊ ⊕ id⟷)) ◎
--          ((id⟷ ⊕ swap₊) ⊕ id⟷)) ◎ (assocl₊ ⊕ id⟷)
--   fully-distribute⟷₂r : {t₁ t₂ t₃ t₄ : U} →
--     ((((dist ◎ (distl ⊕ distl)) ◎ assocl₊) ◎ (assocr₊ ⊕ id⟷)) ◎
--        ((id⟷ ⊕ swap₊) ⊕ id⟷)) ◎ (assocl₊ ⊕ id⟷) ⟷₂
--     (distl ◎ (dist {t₁} {t₂} {t₃} ⊕ dist {t₁} {t₂} {t₄})) ◎ assocl₊

-- infix  2  _▤
-- infixr 2  _⟷₂⟨_⟩_

-- _⟷₂⟨_⟩_ : {t₁ t₂ : U} (c₁ : t₁ ⟷₁ t₂) {c₂ : t₁ ⟷₁ t₂} {c₃ : t₁ ⟷₁ t₂} →
--          (c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₃) → (c₁ ⟷₂ c₃)
-- _ ⟷₂⟨ α ⟩ β = trans⟷₂ α β

-- _▤ : {t₁ t₂ : U} → (c : t₁ ⟷₁ t₂) → (c ⟷₂ c)
-- _▤ c = id⟷₂

-- !-cong : {t₁ t₂ : U} {a b : t₁ ⟷₁ t₂} → (a ⟷₂ b) → (! a ⟷₂ ! b)
-- !-cong assoc◎l = assoc◎r
-- !-cong assoc◎r = assoc◎l
-- !-cong assocl⊕l = assocr⊕l
-- !-cong assocl⊕r = assocr⊕r
-- !-cong assocl⊗l = assocr⊗l
-- !-cong assocl⊗r = assocr⊗r
-- !-cong assocr⊕r = assocl⊕r
-- !-cong assocr⊗l = assocl⊗l
-- !-cong assocr⊗r = assocl⊗r
-- !-cong assocr⊕l = assocl⊕l
-- !-cong dist⟷₂l = factor⟷₂r
-- !-cong dist⟷₂r = factor⟷₂l
-- !-cong distl⟷₂l = factorl⟷₂r
-- !-cong distl⟷₂r = factorl⟷₂l
-- !-cong factor⟷₂l = dist⟷₂r
-- !-cong factor⟷₂r = dist⟷₂l
-- !-cong factorl⟷₂l = distl⟷₂r
-- !-cong factorl⟷₂r = distl⟷₂l
-- !-cong idl◎l = idr◎l
-- !-cong idl◎r = idr◎r
-- !-cong idr◎l = idl◎l
-- !-cong idr◎r = idl◎r
-- !-cong linv◎l = rinv◎l
-- !-cong linv◎r = rinv◎r
-- !-cong rinv◎l = linv◎l
-- !-cong rinv◎r = linv◎r
-- !-cong unite₊l⟷₂l = uniti₊l⟷₂r
-- !-cong unite₊l⟷₂r = uniti₊l⟷₂l
-- !-cong uniti₊l⟷₂l = unite₊l⟷₂r
-- !-cong uniti₊l⟷₂r = unite₊l⟷₂l
-- !-cong unite₊r⟷₂l = uniti₊r⟷₂r
-- !-cong unite₊r⟷₂r = uniti₊r⟷₂l
-- !-cong uniti₊r⟷₂l = unite₊r⟷₂r
-- !-cong uniti₊r⟷₂r = unite₊r⟷₂l
-- !-cong swapl₊⟷₂ = swapr₊⟷₂
-- !-cong swapr₊⟷₂ = swapl₊⟷₂
-- !-cong unitel⋆⟷₂l = unitir⋆⟷₂l
-- !-cong uniter⋆⟷₂l = unitil⋆⟷₂l
-- !-cong unitil⋆⟷₂l = uniter⋆⟷₂l
-- !-cong unitir⋆⟷₂l = unitel⋆⟷₂l
-- !-cong unitel⋆⟷₂r = unitir⋆⟷₂r
-- !-cong uniter⋆⟷₂r = unitil⋆⟷₂r
-- !-cong unitil⋆⟷₂r = uniter⋆⟷₂r
-- !-cong unitir⋆⟷₂r = unitel⋆⟷₂r
-- !-cong swapl⋆⟷₂ = swapr⋆⟷₂
-- !-cong swapr⋆⟷₂ = swapl⋆⟷₂
-- !-cong id⟷₂ = id⟷₂
-- !-cong (trans⟷₂ α β) = trans⟷₂ (!-cong α) (!-cong β)
-- !-cong (α ⊡ β) = (!-cong β) ⊡ (!-cong α)
-- !-cong (resp⊕⟷₂ α β) = resp⊕⟷₂ (!-cong α) (!-cong β)
-- !-cong (resp⊗⟷₂ α β) = resp⊗⟷₂ (!-cong α) (!-cong β)
-- !-cong id⟷⊕id⟷⟷₂ = id⟷⊕id⟷⟷₂
-- !-cong split⊕-id⟷ = split⊕-id⟷
-- !-cong hom⊕◎⟷₂ = hom⊕◎⟷₂
-- !-cong hom◎⊕⟷₂ = hom◎⊕⟷₂
-- !-cong id⟷⊗id⟷⟷₂ = id⟷⊗id⟷⟷₂
-- !-cong split⊗-id⟷ = split⊗-id⟷
-- !-cong hom⊗◎⟷₂ = hom⊗◎⟷₂
-- !-cong hom◎⊗⟷₂ = hom◎⊗⟷₂
-- !-cong triangle⊕l =
--   uniti₊r ⊕ id⟷
--     ⟷₂⟨ {!!} ⟩
--   (id⟷ ⊕ uniti₊l) ◎ assocl₊ ▤
-- !-cong triangle⊕r = {!!}
-- !-cong triangle⊗l = {!!}
-- !-cong triangle⊗r = {!!}
-- !-cong pentagon⊕l = {!!}
-- !-cong pentagon⊕r = {!!}
-- !-cong pentagon⊗l = {!!}
-- !-cong pentagon⊗r = {!!}
-- !-cong unite₊l-coh-l = {!!}
-- !-cong unite₊l-coh-r = {!!}
-- !-cong unite⋆l-coh-l = {!!}
-- !-cong unite⋆l-coh-r = {!!}
-- !-cong hexagonr⊕l = {!!}
-- !-cong hexagonr⊕r = {!!}
-- !-cong hexagonl⊕l = {!!}
-- !-cong hexagonl⊕r = {!!}
-- !-cong hexagonr⊗l = {!!}
-- !-cong hexagonr⊗r = {!!}
-- !-cong hexagonl⊗l = {!!}
-- !-cong hexagonl⊗r = {!!}
-- !-cong absorbl⟷₂l = {!!}
-- !-cong absorbl⟷₂r = {!!}
-- !-cong absorbr⟷₂l = {!!}
-- !-cong absorbr⟷₂r = {!!}
-- !-cong factorzl⟷₂l = {!!}
-- !-cong factorzl⟷₂r = {!!}
-- !-cong factorzr⟷₂l = {!!}
-- !-cong factorzr⟷₂r = {!!}
-- !-cong swap₊distl⟷₂l = {!!}
-- !-cong swap₊distl⟷₂r = {!!}
-- !-cong dist-swap⋆⟷₂l = {!!}
-- !-cong dist-swap⋆⟷₂r = {!!}
-- !-cong assocl₊-dist-dist⟷₂l = {!!}
-- !-cong assocl₊-dist-dist⟷₂r = {!!}
-- !-cong assocl⋆-distl⟷₂l = {!!}
-- !-cong assocl⋆-distl⟷₂r = {!!}
-- !-cong absorbr0-absorbl0⟷₂ = {!!}
-- !-cong absorbl0-absorbr0⟷₂ = {!!}
-- !-cong absorbr⟷₂distl-absorb-unite = {!!}
-- !-cong distl-absorb-unite⟷₂absorbr = {!!}
-- !-cong unite⋆r0-absorbr1⟷₂ = {!!}
-- !-cong absorbr1-unite⋆r-⟷₂ = {!!}
-- !-cong absorbl≡swap⋆◎absorbr = {!!}
-- !-cong swap⋆◎absorbr≡absorbl = {!!}
-- !-cong absorbr⟷₂[assocl⋆◎[absorbr⊗id⟷]]◎absorbr = {!!}
-- !-cong [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⟷₂absorbr = {!!}
-- !-cong [id⟷⊗absorbr]◎absorbl⟷₂assocl⋆◎[absorbl⊗id⟷]◎absorbr = {!!}
-- !-cong assocl⋆◎[absorbl⊗id⟷]◎absorbr⟷₂[id⟷⊗absorbr]◎absorbl = {!!}
-- !-cong elim⊥-A[0⊕B]⟷₂l = {!!}
-- !-cong elim⊥-A[0⊕B]⟷₂r = {!!}
-- !-cong elim⊥-1[A⊕B]⟷₂l = {!!}
-- !-cong elim⊥-1[A⊕B]⟷₂r = {!!}
-- !-cong fully-distribute⟷₂l = {!!}
-- !-cong fully-distribute⟷₂r = {!!}

-- -- At the next level we have a trivial equivalence that equates all
-- -- 2-morphisms of the same type.

-- triv≡ : {t₁ t₂ : U} {f g : t₁ ⟷₁ t₂} → (α β : f ⟷₂ g) → Set
-- triv≡ _ _ = ⊤

-- ------------------------------------------------------------------------------
-- -- Inverses for 2paths

-- 2! : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷₁ t₂} → (c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₁)
-- 2! assoc◎l = assoc◎r
-- 2! assoc◎r = assoc◎l
-- 2! assocl⊕l = assocl⊕r
-- 2! assocl⊕r = assocl⊕l
-- 2! assocl⊗l = assocl⊗r
-- 2! assocl⊗r = assocl⊗l
-- 2! assocr⊕r = assocr⊕l
-- 2! assocr⊕l = assocr⊕r
-- 2! assocr⊗r = assocr⊗l
-- 2! assocr⊗l = assocr⊗r
-- 2! dist⟷₂l = dist⟷₂r
-- 2! dist⟷₂r = dist⟷₂l
-- 2! distl⟷₂l = distl⟷₂r
-- 2! distl⟷₂r = distl⟷₂l
-- 2! factor⟷₂l = factor⟷₂r
-- 2! factor⟷₂r = factor⟷₂l
-- 2! factorl⟷₂l = factorl⟷₂r
-- 2! factorl⟷₂r = factorl⟷₂l
-- 2! idl◎l = idl◎r
-- 2! idl◎r = idl◎l
-- 2! idr◎l = idr◎r
-- 2! idr◎r = idr◎l
-- 2! linv◎l = linv◎r
-- 2! linv◎r = linv◎l
-- 2! rinv◎l = rinv◎r
-- 2! rinv◎r = rinv◎l
-- 2! unite₊l⟷₂l = unite₊l⟷₂r
-- 2! unite₊l⟷₂r = unite₊l⟷₂l
-- 2! uniti₊l⟷₂l = uniti₊l⟷₂r
-- 2! uniti₊l⟷₂r = uniti₊l⟷₂l
-- 2! unite₊r⟷₂l = unite₊r⟷₂r
-- 2! unite₊r⟷₂r = unite₊r⟷₂l
-- 2! uniti₊r⟷₂l = uniti₊r⟷₂r
-- 2! uniti₊r⟷₂r = uniti₊r⟷₂l
-- 2! swapl₊⟷₂ = swapr₊⟷₂
-- 2! swapr₊⟷₂ = swapl₊⟷₂
-- 2! unitel⋆⟷₂l = uniter⋆⟷₂l
-- 2! uniter⋆⟷₂l = unitel⋆⟷₂l
-- 2! unitil⋆⟷₂l = unitir⋆⟷₂l
-- 2! unitir⋆⟷₂l = unitil⋆⟷₂l
-- 2! unitel⋆⟷₂r = uniter⋆⟷₂r
-- 2! uniter⋆⟷₂r = unitel⋆⟷₂r
-- 2! unitil⋆⟷₂r = unitir⋆⟷₂r
-- 2! unitir⋆⟷₂r = unitil⋆⟷₂r
-- 2! swapl⋆⟷₂ = swapr⋆⟷₂
-- 2! swapr⋆⟷₂ = swapl⋆⟷₂
-- 2! id⟷₂ = id⟷₂
-- 2! (α ⊡ β) = (2! α) ⊡ (2! β)
-- 2! (trans⟷₂ α β) = trans⟷₂ (2! β) (2! α)
-- 2! (resp⊕⟷₂ α β) = resp⊕⟷₂ (2! α) (2! β)
-- 2! (resp⊗⟷₂ α β) = resp⊗⟷₂ (2! α) (2! β)
-- 2! id⟷⊕id⟷⟷₂ = split⊕-id⟷
-- 2! split⊕-id⟷ = id⟷⊕id⟷⟷₂
-- 2! hom⊕◎⟷₂ = hom◎⊕⟷₂
-- 2! hom◎⊕⟷₂ = hom⊕◎⟷₂
-- 2! id⟷⊗id⟷⟷₂ = split⊗-id⟷
-- 2! split⊗-id⟷ = id⟷⊗id⟷⟷₂
-- 2! hom⊗◎⟷₂ = hom◎⊗⟷₂
-- 2! hom◎⊗⟷₂ = hom⊗◎⟷₂
-- 2! triangle⊕l = triangle⊕r
-- 2! triangle⊕r = triangle⊕l
-- 2! triangle⊗l = triangle⊗r
-- 2! triangle⊗r = triangle⊗l
-- 2! pentagon⊕l = pentagon⊕r
-- 2! pentagon⊕r = pentagon⊕l
-- 2! pentagon⊗l = pentagon⊗r
-- 2! pentagon⊗r = pentagon⊗l
-- 2! unite₊l-coh-l = unite₊l-coh-r
-- 2! unite₊l-coh-r = unite₊l-coh-l
-- 2! unite⋆l-coh-l = unite⋆l-coh-r
-- 2! unite⋆l-coh-r = unite⋆l-coh-l
-- 2! hexagonr⊕l = hexagonr⊕r
-- 2! hexagonr⊕r = hexagonr⊕l
-- 2! hexagonl⊕l = hexagonl⊕r
-- 2! hexagonl⊕r = hexagonl⊕l
-- 2! hexagonr⊗l = hexagonr⊗r
-- 2! hexagonr⊗r = hexagonr⊗l
-- 2! hexagonl⊗l = hexagonl⊗r
-- 2! hexagonl⊗r = hexagonl⊗l
-- 2! absorbl⟷₂l = absorbl⟷₂r
-- 2! absorbl⟷₂r = absorbl⟷₂l
-- 2! absorbr⟷₂l = absorbr⟷₂r
-- 2! absorbr⟷₂r = absorbr⟷₂l
-- 2! factorzl⟷₂l = factorzl⟷₂r
-- 2! factorzl⟷₂r = factorzl⟷₂l
-- 2! factorzr⟷₂l = factorzr⟷₂r
-- 2! factorzr⟷₂r = factorzr⟷₂l
-- 2! swap₊distl⟷₂l = swap₊distl⟷₂r
-- 2! swap₊distl⟷₂r = swap₊distl⟷₂l
-- 2! dist-swap⋆⟷₂l = dist-swap⋆⟷₂r
-- 2! dist-swap⋆⟷₂r = dist-swap⋆⟷₂l
-- 2! assocl₊-dist-dist⟷₂l = assocl₊-dist-dist⟷₂r
-- 2! assocl₊-dist-dist⟷₂r = assocl₊-dist-dist⟷₂l
-- 2! assocl⋆-distl⟷₂l = assocl⋆-distl⟷₂r
-- 2! assocl⋆-distl⟷₂r = assocl⋆-distl⟷₂l
-- 2! absorbr0-absorbl0⟷₂ = absorbl0-absorbr0⟷₂
-- 2! absorbl0-absorbr0⟷₂ = absorbr0-absorbl0⟷₂
-- 2! absorbr⟷₂distl-absorb-unite = distl-absorb-unite⟷₂absorbr
-- 2! distl-absorb-unite⟷₂absorbr = absorbr⟷₂distl-absorb-unite
-- 2! unite⋆r0-absorbr1⟷₂ = absorbr1-unite⋆r-⟷₂
-- 2! absorbr1-unite⋆r-⟷₂ = unite⋆r0-absorbr1⟷₂
-- 2! absorbl≡swap⋆◎absorbr = swap⋆◎absorbr≡absorbl
-- 2! swap⋆◎absorbr≡absorbl = absorbl≡swap⋆◎absorbr
-- 2! absorbr⟷₂[assocl⋆◎[absorbr⊗id⟷]]◎absorbr =
--     [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⟷₂absorbr
-- 2!  [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⟷₂absorbr =
--     absorbr⟷₂[assocl⋆◎[absorbr⊗id⟷]]◎absorbr
-- 2! [id⟷⊗absorbr]◎absorbl⟷₂assocl⋆◎[absorbl⊗id⟷]◎absorbr =
--     assocl⋆◎[absorbl⊗id⟷]◎absorbr⟷₂[id⟷⊗absorbr]◎absorbl
-- 2! assocl⋆◎[absorbl⊗id⟷]◎absorbr⟷₂[id⟷⊗absorbr]◎absorbl =
--     [id⟷⊗absorbr]◎absorbl⟷₂assocl⋆◎[absorbl⊗id⟷]◎absorbr
-- 2! elim⊥-A[0⊕B]⟷₂l = elim⊥-A[0⊕B]⟷₂r
-- 2! elim⊥-A[0⊕B]⟷₂r = elim⊥-A[0⊕B]⟷₂l
-- 2! elim⊥-1[A⊕B]⟷₂l = elim⊥-1[A⊕B]⟷₂r
-- 2! elim⊥-1[A⊕B]⟷₂r = elim⊥-1[A⊕B]⟷₂l
-- 2! fully-distribute⟷₂l = fully-distribute⟷₂r
-- 2! fully-distribute⟷₂r = fully-distribute⟷₂l


data _⟷₃_ : {X Y : U} {p q : X ⟷₁ Y} → (p ⟷₂ q) → (p ⟷₂ q) → Set where
  trunc : {X Y : U} {p q : X ⟷₁ Y} (α β : p ⟷₂ q) → α ⟷₃ β