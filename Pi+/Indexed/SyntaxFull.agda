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
  unite₊l : O + t ⟷₁ t
  uniti₊l : t ⟷₁ O + t
  unite⋆l : I × t ⟷₁ t
  uniti⋆l : t ⟷₁ I × t
  swap₊   : t₁ + t₂ ⟷₁ t₂ + t₁
  swap⋆   : t₁ × t₂ ⟷₁ t₂ × t₁
  assocl₊ : t₁ + (t₂ + t₃) ⟷₁ (t₁ + t₂) + t₃
  assocr₊ : (t₁ + t₂) + t₃ ⟷₁ t₁ + (t₂ + t₃)
  assocl⋆ : t₁ × (t₂ × t₃) ⟷₁ (t₁ × t₂) × t₃
  assocr⋆ : (t₁ × t₂) × t₃ ⟷₁ t₁ × (t₂ × t₃)
  absorbr : O × t ⟷₁ O
  absorbl : t × O ⟷₁ O
  factorzr : O ⟷₁ t × O
  factorzl : O ⟷₁ O × t
  dist : (t₁ + t₂) × t₃ ⟷₁ (t₁ × t₃) + (t₂ × t₃)
  factor : {t₁ t₂ t₃ : U} → (t₁ × t₃) + (t₂ × t₃) ⟷₁ (t₁ + t₂) × t₃
  id⟷₁  : t ⟷₁ t
  _◎_     : (t₁ ⟷₁ t₂) → (t₂ ⟷₁ t₃) → (t₁ ⟷₁ t₃)
  _⊕_     : (t₁ ⟷₁ t₃) → (t₂ ⟷₁ t₄) → (t₁ + t₂ ⟷₁ t₃ + t₄)
  _⊗_     : (t₁ ⟷₁ t₃) → (t₂ ⟷₁ t₄) → (t₁ × t₂ ⟷₁ t₃ × t₄)

-- Equational reasoning

infixr 10 _⟷₁⟨_⟩_
infix  15 _⟷₁∎

_⟷₁⟨_⟩_ : (t₁ : U) → (t₁ ⟷₁ t₂) → (t₂ ⟷₁ t₃) → (t₁ ⟷₁ t₃)
_ ⟷₁⟨ c₁ ⟩ c₂ = c₁ ◎ c₂

_⟷₁∎ : (t : U) → t ⟷₁ t
_⟷₁∎ t = id⟷₁

-- Coherence

unite₊r : {t : U} → t + O ⟷₁ t
unite₊r = swap₊ ◎ unite₊l

uniti₊r : t ⟷₁ t + O
uniti₊r = uniti₊l ◎ swap₊

unite⋆r : {t : U} → t × I ⟷₁ t
unite⋆r = swap⋆ ◎ unite⋆l

uniti⋆r : t ⟷₁ t × I
uniti⋆r = uniti⋆l ◎ swap⋆

!⟷₁ : t₁ ⟷₁ t₂ → t₂ ⟷₁ t₁
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
