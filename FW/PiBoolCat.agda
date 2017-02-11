{-# OPTIONS --without-K #-}

module PiBoolCat where

open import Level using () renaming (zero to lzero)
open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)

infix 30 _◌_ _●_
infix 20 _⟷_
infix 10 _⇔_

------------------------------------------------------------------------------

data `U : Set where
  `𝟚 : `U

data _⟷_ : `U → `U → Set where
  id   : {A : `U} → A ⟷ A
  swap : `𝟚 ⟷ `𝟚
  _◌_  : {A B C : `U} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)

! : {A B : `U} → (A ⟷ B) → (B ⟷ A)
! id = id
! swap = swap
! (c₁ ◌ c₂) = ! c₂ ◌ ! c₁

data _⇔_ : {A B : `U} → (A ⟷ B) → (A ⟷ B) → Set where
  id     : {A B : `U} {c : A ⟷ B} → c ⇔ c
  assocl : {A B C D : `U} {c₁ : A ⟷ C} {c₂ : C ⟷ D} {c₃ : D ⟷ B} →
          c₁ ◌ (c₂ ◌ c₃) ⇔ (c₁ ◌ c₂) ◌ c₃
  assocr : {A B C D : `U} {c₁ : A ⟷ C} {c₂ : C ⟷ D} {c₃ : D ⟷ B} →
          (c₁ ◌ c₂) ◌ c₃ ⇔ c₁ ◌ (c₂ ◌ c₃)
  idll   : {A B : `U} {c : A ⟷ B} → id ◌ c ⇔ c
  idlr   : {A B : `U} {c : A ⟷ B} → c ⇔ id ◌ c
  idrl   : {A B : `U} {c : A ⟷ B} → c ◌ id ⇔ c
  idrr   : {A B : `U} {c : A ⟷ B} → c ⇔ c ◌ id
  invll  : {A B : `U} {c : A ⟷ B} → c ◌ ! c ⇔ id
  invlr  : {A B : `U} {c : A ⟷ B} → id ⇔ c ◌ ! c
  invrl  : {A B : `U} {c : A ⟷ B} → ! c ◌ c ⇔ id
  invrr  : {A B : `U} {c : A ⟷ B} → id ⇔ ! c ◌ c
  _●_    : {A B : `U} {c₁ c₂ c₃ : A ⟷ B} → (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊙_    : {A B C : `U} {c₁ c₁' : A ⟷ B} {c₂ c₂' : B ⟷ C} →
           (c₁ ⇔ c₁') → (c₂ ⇔ c₂') → (c₁ ◌ c₂ ⇔ c₁' ◌ c₂')

2! : {A B : `U} {c₁ c₂ : A ⟷ B} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
2! id = id
2! assocl = assocr
2! assocr = assocl
2! idll = idlr
2! idlr = idll
2! idrl = idrr
2! idrr = idrl
2! invll = invlr
2! invlr = invll
2! invrl = invrr
2! invrr = invrl
2! (α ● β) = 2! β ● 2! α
2! (α ⊙ β) = 2! α ⊙ 2! β

--

PiBoolCat : Category lzero lzero lzero
PiBoolCat = record
  { Obj = `U
  ; _⇒_ = _⟷_
  ; _≡_ = _⇔_
  ; id = id
  ; _∘_ = λ y⟷z x⟷y → x⟷y ◌ y⟷z
  ; assoc = assocl
  ; identityˡ = idrl
  ; identityʳ = idll
  ; equiv = record { refl = id; sym = 2!; trans = _●_ }
  ; ∘-resp-≡ = λ f g → g ⊙ f
  }

Pi1Groupoid : Groupoid PiBoolCat
Pi1Groupoid = record
  { _⁻¹ = !
  ; iso = record { isoˡ = invll ; isoʳ = invrl }
  }

------------------------------------------------------------------------------
