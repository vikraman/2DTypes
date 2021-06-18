{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.PiLevel0 where

open import lib.Base
open import lib.PathGroupoid
import lib.types.Nat as N
open import lib.types.Sigma renaming (_×_ to _X_)
open import lib.types.Fin

open import Pi+.Misc as N
open import Pi+.Extra

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

∣_∣ : U → ℕ
∣ O ∣ = 0
∣ I ∣ = 1
∣ t₁ + t₂ ∣ = ∣ t₁ ∣ N.+ ∣ t₂ ∣
∣ t₁ × t₂ ∣ = ∣ t₁ ∣ N.* ∣ t₂ ∣

private
  variable
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

-- Simple denotational semantics

postulate
  *-unit-r : (n : ℕ) → n N.* 0 == 0
  decomp+ : (t₁ t₂ : U) → Fin ∣ t₁ + t₂ ∣ → Fin ∣ t₁ ∣ ⊎ Fin ∣ t₂ ∣
  comp+ : (t₁ t₂ : U) → Fin ∣ t₁ ∣ ⊎ Fin ∣ t₂ ∣ → Fin ∣ t₁ + t₂ ∣
  decomp* : (t₁ t₂ : U) → Fin ∣ t₁ × t₂ ∣ → Fin ∣ t₁ ∣ X Fin ∣ t₂ ∣
  comp* : (t₁ t₂ : U) → Fin ∣ t₁ ∣ X Fin ∣ t₂ ∣ → Fin ∣ t₁ × t₂ ∣

swap+Fin : {t₁ t₂ : U} → Fin ∣ t₁ ∣ ⊎ Fin ∣ t₂ ∣ → Fin ∣ t₂ ∣ ⊎ Fin ∣ t₁ ∣
swap+Fin (inj₁ v) = inj₂ v
swap+Fin (inj₂ v) = inj₁ v

swap*Fin : {t₁ t₂ : U} → Fin ∣ t₁ ∣ X Fin ∣ t₂ ∣ → Fin ∣ t₂ ∣ X Fin ∣ t₁ ∣
swap*Fin (v , w) = (w , v)

semT : (t : U) → Set
semT t = Fin ∣ t ∣

semC : {t₁ t₂ : U} → (c : t₁ ⟷₁ t₂) → Fin ∣ t₁ ∣ → Fin ∣ t₂ ∣
semC unite₊l = idf _
semC uniti₊l = idf _
semC {I × t₂} {t₂} unite⋆l = transport Fin (N.+-unit-r ∣ t₂ ∣)
semC {t₁} {I × t₁} uniti⋆l = transport Fin (! (N.+-unit-r ∣ t₁ ∣))
semC {t₁ + t₂} {t₂ + t₁} swap₊ = (comp+ t₂ t₁) ∘ (swap+Fin {t₁} {t₂}) ∘ (decomp+ t₁ t₂)
semC {t₁ × t₂} {t₂ × t₁} swap⋆ = (comp* t₂ t₁) ∘ (swap*Fin {t₁} {t₂}) ∘ (decomp* t₁ t₂)
semC assocl₊ = {!!} -- n = {!!}
semC assocr₊ = {!!} -- n = {!!}
semC assocl⋆ = {!!} -- n = {!!}
semC assocr⋆ = {!!} -- n = {!!}
semC absorbr ()
semC {t × O} {O} absorbl = transport Fin (*-unit-r ∣ t ∣)
semC factorzr ()
semC factorzl ()
semC dist n = {!!} -- = {!!}
semC factor = {!!} -- n = {!!}
semC id⟷₁ n = n
semC (c₁ ◎ c₂) = semC c₂ ∘ semC c₁
semC (c₁ ⊕ c₂) = {!!} -- n = {!!}
semC (c₁ ⊗ c₂) = {!!} -- n = {!!}

{--

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

open import PiU using (U; ZERO; ONE; PLUS; TIMES; toℕ)

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
  id⟷    : {t : U} → t ⟷ t
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} →
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)

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

------------------------------------------------------------------------------
--}
