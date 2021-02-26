{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Base
open import lib.NType
open import lib.PathGroupoid
import lib.types.Nat as N

open import Pi+.Misc
open import Pi+.Extra

module Pi+.Indexed.Syntax where

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

-- postulate
--   =↦ : ∀ {i} {A : Type i} {a b : A} → a == b → a ↦ b

-- +-assoc-↦ : (k m n : ℕ) → (k N.+ m) N.+ n ↦ k N.+ (m N.+ n)
-- +-assoc-↦ k m n = =↦ (N.+-assoc k m n)
-- {-# REWRITE +-assoc-↦ #-}

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

-- Equational reasoning

infixr 10 _⟷₁⟨_⟩_
infix  15 _⟷₁∎

_⟷₁⟨_⟩_ : (t₁ : U n) → (t₁ ⟷₁ t₂) → (t₂ ⟷₁ t₃) → (t₁ ⟷₁ t₃)
_ ⟷₁⟨ c₁ ⟩ c₂ = c₁ ◎ c₂

_⟷₁∎ : (t : U n) → t ⟷₁ t
_⟷₁∎ t = id⟷₁


⟷₁-eq-size : {n m : ℕ} {t₁ : U n} {t₂ : U m} -> (t₁ ⟷₁ t₂) -> n == m
⟷₁-eq-size unite₊l = idp
⟷₁-eq-size uniti₊l = idp
⟷₁-eq-size (swap₊ {m} {_} {n}) = N.+-comm m n
⟷₁-eq-size (assocl₊ {m} {_} {n} {_} {o}) = ! (N.+-assoc m n o)
⟷₁-eq-size (assocr₊ {m} {_} {n} {_} {o}) = N.+-assoc m n o
⟷₁-eq-size id⟷₁ = idp
⟷₁-eq-size (c ◎ c₁) = (⟷₁-eq-size c) ∙ ⟷₁-eq-size c₁
⟷₁-eq-size (c ⊕ c₁) = ap2 N._+_ (⟷₁-eq-size c) (⟷₁-eq-size c₁)

-- Coherence

-- +-unit-r-↦ : (m : ℕ) → m N.+ 0 ↦ m
-- +-unit-r-↦ m = =↦ (N.+-unit-r m)
-- {-# REWRITE +-unit-r-↦ #-}

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
  trans⟷₂  : {c₁ c₂ c₃ : t₁ ⟷₁ t₂} →
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
  -- Braiding compatible with unitors (redundant; provable from above
  -- axioms. See for example Thm. 10 in "On MacLane's Conditions for
  -- Coherence of Natural Associativities, Commutativities, etc.
  -- Kelly 1964)
  -- unit-braid : unite₊l {O} ⟷₂ swap₊ ◎ unite₊l
  -- braid-unit : swap₊ ◎ unite₊l ⟷₂ unite₊l {O}

-- -- Equational reasoning

infixr 10 _⟷₂⟨_⟩_
infix  15 _⟷₂∎

_⟷₂⟨_⟩_ : ∀ (c₁ : t₁ ⟷₁ t₂) {c₂ c₃ : t₁ ⟷₁ t₂} →
         (c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₃) → (c₁ ⟷₂ c₃)
_ ⟷₂⟨ β ⟩ γ = trans⟷₂ β γ

_⟷₂∎ : ∀ (c : t₁ ⟷₁ t₂) → c ⟷₂ c
_ ⟷₂∎ = id⟷₂

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
!⟷₂ (trans⟷₂ c c₁) = trans⟷₂ (!⟷₂ c₁) (!⟷₂ c)
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

!⟷₁⟷₂ : {c₁ c₂ : t₁ ⟷₁ t₂} → (α : c₁ ⟷₂ c₂) → (!⟷₁ c₁ ⟷₂ !⟷₁ c₂)
!⟷₁⟷₂ assoc◎l = assoc◎r
!⟷₁⟷₂ assoc◎r = assoc◎l
!⟷₁⟷₂ assocl₊l = assocr₊l
!⟷₁⟷₂ assocl₊r = assocr₊r
!⟷₁⟷₂ assocr₊r = assocl₊r
!⟷₁⟷₂ assocr₊l = assocl₊l
!⟷₁⟷₂ idl◎l = idr◎l
!⟷₁⟷₂ idl◎r = idr◎r
!⟷₁⟷₂ idr◎l = idl◎l
!⟷₁⟷₂ idr◎r = idl◎r
!⟷₁⟷₂ linv◎l = rinv◎l
!⟷₁⟷₂ linv◎r = rinv◎r
!⟷₁⟷₂ rinv◎l = linv◎l
!⟷₁⟷₂ rinv◎r = linv◎r
!⟷₁⟷₂ unite₊l⟷₂l = uniti₊l⟷₂r
!⟷₁⟷₂ unite₊l⟷₂r = uniti₊l⟷₂l
!⟷₁⟷₂ uniti₊l⟷₂l = unite₊l⟷₂r
!⟷₁⟷₂ uniti₊l⟷₂r = unite₊l⟷₂l
!⟷₁⟷₂ swapl₊⟷₂ = swapr₊⟷₂
!⟷₁⟷₂ swapr₊⟷₂ = swapl₊⟷₂
!⟷₁⟷₂ id⟷₂ = id⟷₂
!⟷₁⟷₂ (trans⟷₂ α β) = trans⟷₂ (!⟷₁⟷₂ α) (!⟷₁⟷₂ β)
!⟷₁⟷₂ (α ⊡ β) = !⟷₁⟷₂ β ⊡ !⟷₁⟷₂ α
!⟷₁⟷₂ (resp⊕⟷₂ α β) = resp⊕⟷₂ (!⟷₁⟷₂ α) (!⟷₁⟷₂ β)
!⟷₁⟷₂ id⟷₁⊕id⟷₁⟷₂ = id⟷₁⊕id⟷₁⟷₂
!⟷₁⟷₂ split⊕-id⟷₁ = split⊕-id⟷₁
!⟷₁⟷₂ hom⊕◎⟷₂ = hom⊕◎⟷₂
!⟷₁⟷₂ hom◎⊕⟷₂ = hom◎⊕⟷₂
!⟷₁⟷₂ triangle₊l =
  ((uniti₊l ◎ swap₊) ⊕ id⟷₁)
    ⟷₂⟨ TODO ⟩
  ((id⟷₁ ⊕ uniti₊l) ◎ assocl₊) ⟷₂∎
!⟷₁⟷₂ triangle₊r =
  ((id⟷₁ ⊕ uniti₊l) ◎ assocl₊)
    ⟷₂⟨ TODO ⟩
  ((uniti₊l ◎ swap₊) ⊕ id⟷₁) ⟷₂∎
!⟷₁⟷₂ pentagon₊l = TODO
!⟷₁⟷₂ pentagon₊r = TODO
!⟷₁⟷₂ unite₊l-coh-l = TODO
!⟷₁⟷₂ unite₊l-coh-r = TODO
!⟷₁⟷₂ hexagonr₊l = trans⟷₂ (trans⟷₂ assoc◎l hexagonl₊l) assoc◎r
!⟷₁⟷₂ hexagonr₊r = trans⟷₂ (trans⟷₂ assoc◎l hexagonl₊r) assoc◎r
!⟷₁⟷₂ hexagonl₊l = trans⟷₂ (trans⟷₂ assoc◎l hexagonr₊l) assoc◎r
!⟷₁⟷₂ hexagonl₊r = trans⟷₂ (trans⟷₂ assoc◎l hexagonr₊r) assoc◎r

-- -- 3-combinators trivial

data _⟷₃_ : {X Y : U n} {p q : X ⟷₁ Y} → (p ⟷₂ q) → (p ⟷₂ q) → Set where
  trunc : {X Y : U n} {p q : X ⟷₁ Y} (α β : p ⟷₂ q) → α ⟷₃ β

-- --
