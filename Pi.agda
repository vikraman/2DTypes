{-# OPTIONS --without-K #-}

module Pi where

open import Data.Nat using (ℕ; _+_; _*_)

------------------------------------------------------------------------------
-- Define the ``universe'' for Pi.  All versions of Pi share the same
-- universe.  Where they differ is in what combinators exist between
-- members of the universe.
--
-- ZERO is a type with no elements
-- ONE is a type with one element 'tt'
-- PLUS ONE ONE is a type with elements 'false' and 'true'
-- and so on for all finite types built from ZERO, ONE, PLUS, and TIMES
--
-- We also have that U is a type with elements ZERO, ONE, PLUS ONE ONE,
--   TIMES BOOL BOOL, etc.

data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

-- defines the size of a finite type

toℕ : U → ℕ
toℕ ZERO = 0
toℕ ONE = 1
toℕ (PLUS t₁ t₂) = toℕ t₁ + toℕ t₂
toℕ (TIMES t₁ t₂) = toℕ t₁ * toℕ t₂

-- We refine the trivial relation used in level-(-2). We do not
-- identify all types: only those of the same "size". So between any
-- two types, there could be zero, one, or many identifications. If
-- there is more than one idenfication we force them to be the same;
-- so 'id' and 'not' at BOOL ⟷ BOOL are the same and U effectively
-- collapses to the set of natural numbers

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Relation.Binary.Core using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong₂; module ≡-Reasoning)

infix  30 _⟷_
infixr 50 _◎_

------------------------------------------------------------------------------
-- Level 0 of Pi

-- Abbreviation

size : U → ℕ
size = toℕ

-- Combinators

data _⟷_ : U → U → Set where
  unite₊l : {t : U} → PLUS ZERO t ⟷ t
  uniti₊l : {t : U} → t ⟷ PLUS ZERO t
  unite₊r : {t : U} → PLUS t ZERO ⟷ t
  uniti₊r : {t : U} → t ⟷ PLUS t ZERO
  swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆l  : {t : U} → TIMES ONE t ⟷ t
  uniti⋆l  : {t : U} → t ⟷ TIMES ONE t
  unite⋆r : {t : U} → TIMES t ONE ⟷ t
  uniti⋆r : {t : U} → t ⟷ TIMES t ONE
  swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  absorbr : {t : U} → TIMES ZERO t ⟷ ZERO
  absorbl : {t : U} → TIMES t ZERO ⟷ ZERO
  factorzr : {t : U} → ZERO ⟷ TIMES t ZERO
  factorzl : {t : U} → ZERO ⟷ TIMES ZERO t
  dist    : {t₁ t₂ t₃ : U} →
            TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)
  factor  : {t₁ t₂ t₃ : U} →
            PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  distl   : {t₁ t₂ t₃ : U } →
            TIMES t₁ (PLUS t₂ t₃) ⟷ PLUS (TIMES t₁ t₂) (TIMES t₁ t₃)
  factorl : {t₁ t₂ t₃ : U } →
            PLUS (TIMES t₁ t₂) (TIMES t₁ t₃) ⟷ TIMES t₁ (PLUS t₂ t₃)
  id⟷    : {t : U} → t ⟷ t
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} →
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : U} →
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)

-- At the next level we have a trivial equivalence that equates all
-- morphisms of the same type so for example id and not : BOOL ⟷ BOOL
-- are equated

triv≡ : {t₁ t₂ : U} → (f g : t₁ ⟷ t₂) → Set
triv≡ _ _ = ⊤

triv≡Equiv : {t₁ t₂ : U} → IsEquivalence (triv≡ {t₁} {t₂})
triv≡Equiv = record
  { refl = tt
  ; sym = λ _ → tt
  ; trans = λ _ _ → tt
  }

------------------------------------------------------------------------------
-- Every combinator has an inverse. There are actually many
-- syntactically different inverses but they are all equivalent.

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
! id⟷       = id⟷
! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁
! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
! (c₁ ⊗ c₂) = (! c₁) ⊗ (! c₂)

!! : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → triv≡ (! (! c)) c
!! = tt

!!2 : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → ! (! c) ≡ c
!!2 {c = unite₊l} = refl
!!2 {c = uniti₊l} = refl
!!2 {c = unite₊r} = refl
!!2 {c = uniti₊r} = refl
!!2 {c = swap₊} = refl
!!2 {c = assocl₊} = refl
!!2 {c = assocr₊} = refl
!!2 {c = unite⋆l} = refl
!!2 {c = uniti⋆l} = refl
!!2 {c = unite⋆r} = refl
!!2 {c = uniti⋆r} = refl
!!2 {c = swap⋆} = refl
!!2 {c = assocl⋆} = refl
!!2 {c = assocr⋆} = refl
!!2 {c = absorbr} = refl
!!2 {c = absorbl} = refl
!!2 {c = factorzr} = refl
!!2 {c = factorzl} = refl
!!2 {c = dist} = refl
!!2 {c = factor} = refl
!!2 {c = distl} = refl
!!2 {c = factorl} = refl
!!2 {c = id⟷} = refl
!!2 {c = c ◎ c₁} = cong₂ _◎_ !!2 !!2
!!2 {c = c ⊕ c₁} = cong₂ _⊕_ !!2 !!2
!!2 {c = c ⊗ c₁} = cong₂ _⊗_ !!2 !!2

------------------------------------------------------------------------------
