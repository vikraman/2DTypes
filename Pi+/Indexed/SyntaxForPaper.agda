{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Base
open import lib.NType
open import lib.PathFunctor
open import lib.PathGroupoid
import lib.types.Nat as N

open import Pi+.Misc
open import Pi+.Extra

module Pi+.Indexed.SyntaxForPaper where

private
  variable
    m n o p q r : ℕ

-- Types

data U : ℕ → Type₀ where
  O : U 0
  I : U 1
  _+_ : U m → U n → U (m N.+ n)

infixr 40 _+_
infix 30 _⟷₁_
infixr 50 _◎_ _⊕_

private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U n

-- 1-combinators

data _⟷₁_  : U m → U n → Type₀ where
  unite₊l : O + t ⟷₁ t
  uniti₊l : t ⟷₁ O + t
  swap₊   : t₁ + t₂ ⟷₁ t₂ + t₁
  assocl₊ : t₁ + (t₂ + t₃) ⟷₁ (t₁ + t₂) + t₃
  assocr₊ : (t₁ + t₂) + t₃ ⟷₁ t₁ + (t₂ + t₃)
  id⟷₁  : t ⟷₁ t
  _◎_     : (t₁ ⟷₁ t₂) → (t₂ ⟷₁ t₃) → (t₁ ⟷₁ t₃)
  _⊕_     : (t₁ ⟷₁ t₃) → (t₂ ⟷₁ t₄) → (t₁ + t₂ ⟷₁ t₃ + t₄)

-- Coherence

unite₊r : {t : U n} → t + O ⟷₁ t
unite₊r = swap₊ ◎ unite₊l

uniti₊r : t ⟷₁ t + O
uniti₊r = uniti₊l ◎ swap₊

!⟷₁ : t₁ ⟷₁ t₂ → t₂ ⟷₁ t₁
!⟷₁ unite₊l = uniti₊l
!⟷₁ uniti₊l = unite₊l
!⟷₁ swap₊ = swap₊
!⟷₁ assocl₊ = assocr₊
!⟷₁ assocr₊ = assocl₊
!⟷₁ id⟷₁ = id⟷₁
!⟷₁ (c₁ ◎ c₂) = !⟷₁ c₂ ◎ !⟷₁ c₁
!⟷₁ (c₁ ⊕ c₂) = !⟷₁ c₁ ⊕ !⟷₁ c₂

-- 2-combinators

data _⟷₂_ : {X : U m} {Y : U n} → X ⟷₁ Y → X ⟷₁ Y → Set where
  assoc◎l : {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₃ ⟷₁ t₄} →
          (c₁ ◎ (c₂ ◎ c₃)) ⟷₂ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₃ ⟷₁ t₄} →
          ((c₁ ◎ c₂) ◎ c₃) ⟷₂ (c₁ ◎ (c₂ ◎ c₃))
  assocl₊l : {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊) ⟷₂ (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃))
  assocl₊r : {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃)) ⟷₂ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊)
  assocr₊r : {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⟷₂ (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃)))
  assocr₊l : {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
           (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))) ⟷₂ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
  idl◎l   : {c : t₁ ⟷₁ t₂} → (id⟷₁ ◎ c) ⟷₂ c
  idl◎r   : {c : t₁ ⟷₁ t₂} → c ⟷₂ id⟷₁ ◎ c
  idr◎l   : {c : t₁ ⟷₁ t₂} → (c ◎ id⟷₁) ⟷₂ c
  idr◎r   : {c : t₁ ⟷₁ t₂} → c ⟷₂ (c ◎ id⟷₁)
  linv◎l  : {c : t₁ ⟷₁ t₂} → (c ◎ !⟷₁ c) ⟷₂ id⟷₁
  linv◎r  : {c : t₁ ⟷₁ t₂} → id⟷₁ ⟷₂ (c ◎ !⟷₁ c)
  rinv◎l  : {c : t₁ ⟷₁ t₂} → (!⟷₁ c ◎ c) ⟷₂ id⟷₁
  rinv◎r  : {c : t₁ ⟷₁ t₂} → id⟷₁ ⟷₂ (!⟷₁ c ◎ c)
  unite₊l⟷₂l : {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          (unite₊l ◎ c₂) ⟷₂ ((c₁ ⊕ c₂) ◎ unite₊l)
  unite₊l⟷₂r : {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          ((c₁ ⊕ c₂) ◎ unite₊l) ⟷₂ (unite₊l ◎ c₂)
  uniti₊l⟷₂l : {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          (uniti₊l ◎ (c₁ ⊕ c₂)) ⟷₂ (c₂ ◎ uniti₊l)
  uniti₊l⟷₂r : {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          (c₂ ◎ uniti₊l) ⟷₂ (uniti₊l ◎ (c₁ ⊕ c₂))
  swapl₊⟷₂ : {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} →
          (swap₊ ◎ (c₁ ⊕ c₂)) ⟷₂ ((c₂ ⊕ c₁) ◎ swap₊)
  swapr₊⟷₂ : {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} →
          ((c₂ ⊕ c₁) ◎ swap₊) ⟷₂ (swap₊ ◎ (c₁ ⊕ c₂))
  id⟷₂     : {c : t₁ ⟷₁ t₂} → c ⟷₂ c
  _■_  : {c₁ c₂ c₃ : t₁ ⟷₁ t₂} →
         (c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₃) → (c₁ ⟷₂ c₃)
  _⊡_  : {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₁ ⟷₁ t₂} {c₄ : t₂ ⟷₁ t₃} →
         (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ◎ c₂) ⟷₂ (c₃ ◎ c₄)
  resp⊕⟷₂  :
         {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₁ ⟷₁ t₂} {c₄ : t₃ ⟷₁ t₄} →
         (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ⊕ c₂) ⟷₂ (c₃ ⊕ c₄)
  id⟷₁⊕id⟷₁⟷₂ : (id⟷₁ {t = t₁} ⊕ id⟷₁ {t = t₂}) ⟷₂ id⟷₁
  split⊕-id⟷₁ : (id⟷₁ {t = t₁ + t₂}) ⟷₂ (id⟷₁ ⊕ id⟷₁)
  hom⊕◎⟷₂ : {c₁ : t₅ ⟷₁ t₁} {c₂ : t₆ ⟷₁ t₂}
        {c₃ : t₁ ⟷₁ t₃} {c₄ : t₂ ⟷₁ t₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⟷₂ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⟷₂ : {c₁ : t₅ ⟷₁ t₁} {c₂ : t₆ ⟷₁ t₂}
        {c₃ : t₁ ⟷₁ t₃} {c₄ : t₂ ⟷₁ t₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⟷₂ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
  -- associativity triangle
  triangle₊l :
    (unite₊r {t = t₁} ⊕ id⟷₁ {t = t₂}) ⟷₂ assocr₊ ◎ (id⟷₁ ⊕ unite₊l)
  triangle₊r :
    assocr₊ ◎ (id⟷₁ {t = t₁} ⊕ unite₊l {t = t₂}) ⟷₂ unite₊r ⊕ id⟷₁
  pentagon₊l :
    assocr₊ ◎ (assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃ + t₄}) ⟷₂
    ((assocr₊ ⊕ id⟷₁) ◎ assocr₊) ◎ (id⟷₁ ⊕ assocr₊)
  pentagon₊r :
    ((assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃} ⊕ id⟷₁ {t = t₄}) ◎ assocr₊) ◎ (id⟷₁ ⊕ assocr₊) ⟷₂
    assocr₊ ◎ assocr₊
--   -- unit coherence
  unite₊l-coh-l : unite₊l {t = t₁} ⟷₂ swap₊ ◎ unite₊r
  unite₊l-coh-r : swap₊ ◎ unite₊r ⟷₂ unite₊l {t = t₁}
  hexagonr₊l :
    (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃} ⟷₂
    ((swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ (id⟷₁ ⊕ swap₊)
  hexagonr₊r :
    ((swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ (id⟷₁ ⊕ swap₊) ⟷₂
    (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}
  hexagonl₊l :
    (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃} ⟷₂
    ((id⟷₁ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷₁)
  hexagonl₊r :
    ((id⟷₁ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷₁) ⟷₂
    (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}

-- -- Coherence

!⟷₁!⟷₁ : (c : t₁ ⟷₁ t₂) → (!⟷₁ (!⟷₁ c) ⟷₂ c)
!⟷₁!⟷₁ unite₊l = id⟷₂
!⟷₁!⟷₁ uniti₊l = id⟷₂
!⟷₁!⟷₁ swap₊ = id⟷₂
!⟷₁!⟷₁ assocl₊ = id⟷₂
!⟷₁!⟷₁ assocr₊ = id⟷₂
!⟷₁!⟷₁ id⟷₁ = id⟷₂
!⟷₁!⟷₁ (c ◎ c₁) = !⟷₁!⟷₁ c ⊡ !⟷₁!⟷₁ c₁
!⟷₁!⟷₁ (c ⊕ c₁) = resp⊕⟷₂ (!⟷₁!⟷₁ c) (!⟷₁!⟷₁ c₁)

!⟷₂ : {c₁ c₂ : t₁ ⟷₁ t₂} → (α : c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₁)
!⟷₂ assoc◎l = assoc◎r
!⟷₂ assoc◎r = assoc◎l
!⟷₂ assocl₊l = assocl₊r
!⟷₂ assocl₊r = assocl₊l
!⟷₂ assocr₊r = assocr₊l
!⟷₂ assocr₊l = assocr₊r
!⟷₂ idl◎l = idl◎r
!⟷₂ idl◎r = idl◎l
!⟷₂ idr◎l = idr◎r
!⟷₂ idr◎r = idr◎l
!⟷₂ linv◎l = linv◎r
!⟷₂ linv◎r = linv◎l
!⟷₂ rinv◎l = rinv◎r
!⟷₂ rinv◎r = rinv◎l
!⟷₂ unite₊l⟷₂l = unite₊l⟷₂r
!⟷₂ unite₊l⟷₂r = unite₊l⟷₂l
!⟷₂ uniti₊l⟷₂l = uniti₊l⟷₂r
!⟷₂ uniti₊l⟷₂r = uniti₊l⟷₂l
!⟷₂ swapl₊⟷₂ = swapr₊⟷₂
!⟷₂ swapr₊⟷₂ = swapl₊⟷₂
!⟷₂ id⟷₂ = id⟷₂
!⟷₂ (_■_ c c₁) = _■_ (!⟷₂ c₁) (!⟷₂ c)
!⟷₂ (c ⊡ c₁) = !⟷₂ c ⊡ !⟷₂ c₁
!⟷₂ (resp⊕⟷₂ c c₁) = resp⊕⟷₂ (!⟷₂ c) (!⟷₂ c₁)
!⟷₂ id⟷₁⊕id⟷₁⟷₂ = split⊕-id⟷₁
!⟷₂ split⊕-id⟷₁ = id⟷₁⊕id⟷₁⟷₂
!⟷₂ hom⊕◎⟷₂ = hom◎⊕⟷₂
!⟷₂ hom◎⊕⟷₂ = hom⊕◎⟷₂
!⟷₂ triangle₊l = triangle₊r
!⟷₂ triangle₊r = triangle₊l
!⟷₂ pentagon₊l = pentagon₊r
!⟷₂ pentagon₊r = pentagon₊l
!⟷₂ unite₊l-coh-l = unite₊l-coh-r
!⟷₂ unite₊l-coh-r = unite₊l-coh-l
!⟷₂ hexagonr₊l = hexagonr₊r
!⟷₂ hexagonr₊r = hexagonr₊l
!⟷₂ hexagonl₊l = hexagonl₊r
!⟷₂ hexagonl₊r = hexagonl₊l

-- -- 3-combinators trivial

data _⟷₃_ : {X Y : U n} {p q : X ⟷₁ Y} → (p ⟷₂ q) → (p ⟷₂ q) → Set where
  trunc : {X Y : U n} {p q : X ⟷₁ Y} (α β : p ⟷₂ q) → α ⟷₃ β

-- --
