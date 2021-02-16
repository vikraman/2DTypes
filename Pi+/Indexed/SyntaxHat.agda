{-# OPTIONS --without-K  --rewriting #-}

module Pi+.Indexed.SyntaxHat where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.types.Sigma
open import lib.PathOver

open import lib.PathGroupoid

open import lib.Equivalence
import lib.types.Nat as N

open import Pi+.Extra
open import Pi+.Misc

private
    variable
      m n o p q r : ℕ

-- Types

private
    variable
      t t₁ t₂ t₃ t₄ t₅ t₆ : ℕ

infix 30 _⟷₁^_
infixr 50 _◎^_ ⊕^_

ℕ-p : {n : ℕ} -> (p : n == n) -> p == idp
ℕ-p p = (prop-has-all-paths {{has-level-apply N.ℕ-level _ _}} p idp)

-- 1-combinators

data _⟷₁^_  : ℕ → ℕ → Type₀ where
  swap₊^   : (S (S n)) ⟷₁^ (S (S n))
  id⟷₁^    : n ⟷₁^ n
  _◎^_     : (n ⟷₁^ m) → (m ⟷₁^ o) → (n ⟷₁^ o)
  ⊕^_      : (n ⟷₁^ m) → ((S n) ⟷₁^ (S m))

!⟷₁^ : t₁ ⟷₁^ t₂ → t₂ ⟷₁^ t₁
!⟷₁^ swap₊^ = swap₊^
!⟷₁^ id⟷₁^ = id⟷₁^
!⟷₁^ (c₁ ◎^ c₂) = !⟷₁^ c₂ ◎^ !⟷₁^ c₁
!⟷₁^ (⊕^ c₁) = ⊕^ (!⟷₁^ c₁)

⟷₁^-eq-size : (n ⟷₁^ m) -> n == m
⟷₁^-eq-size swap₊^ = idp
⟷₁^-eq-size id⟷₁^ = idp
⟷₁^-eq-size (c₁ ◎^ c₂) = ⟷₁^-eq-size c₁ ∙ ⟷₁^-eq-size c₂
⟷₁^-eq-size (⊕^ c) = ap S (⟷₁^-eq-size c)

postulate
    ⟷₁^-eq-size-rewrite : {c : t ⟷₁^ t} → (⟷₁^-eq-size c) ↦ idp -- because proof of == in ℕ
    {-# REWRITE ⟷₁^-eq-size-rewrite #-}

big-swap₊^ : n ⟷₁^ m → (S (S n)) ⟷₁^ (S (S m))
big-swap₊^ c with (⟷₁^-eq-size c)
... | idp = swap₊^

-- -- -- 2-combinators

data _⟷₂^_ : n ⟷₁^ m → n ⟷₁^ m → Set where
  assoc◎l^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₂ ⟷₁^ t₃} {c₃ : t₃ ⟷₁^ t₄} →
          (c₁ ◎^ (c₂ ◎^ c₃)) ⟷₂^ ((c₁ ◎^ c₂) ◎^ c₃)
  assoc◎r^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₂ ⟷₁^ t₃} {c₃ : t₃ ⟷₁^ t₄} →
          ((c₁ ◎^ c₂) ◎^ c₃) ⟷₂^ (c₁ ◎^ (c₂ ◎^ c₃))
  -- assocl₊l^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₃ ⟷₁^ t₄} {c₃ : t₅ ⟷₁^ t₆} →
  --         ((c₁ ⊕ (c₂ ⊕ c₃)) ◎^ assocl₊) ⟷₂^ (assocl₊ ◎^ ((c₁ ⊕ c₂) ⊕ c₃))
  -- assocl₊r^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₃ ⟷₁^ t₄} {c₃ : t₅ ⟷₁^ t₆} →
  --         (assocl₊ ◎^ ((c₁ ⊕ c₂) ⊕ c₃)) ⟷₂^ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎^ assocl₊)
  -- assocr₊r^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₃ ⟷₁^ t₄} {c₃ : t₅ ⟷₁^ t₆} →
  --         (((c₁ ⊕ c₂) ⊕ c₃) ◎^ assocr₊) ⟷₂^ (assocr₊ ◎^ (c₁ ⊕ (c₂ ⊕ c₃)))
  -- assocr₊l^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₃ ⟷₁^ t₄} {c₃ : t₅ ⟷₁^ t₆} →
  --          (assocr₊ ◎^ (c₁ ⊕ (c₂ ⊕ c₃))) ⟷₂^ (((c₁ ⊕ c₂) ⊕ c₃) ◎^ assocr₊)
  idl◎l^   : {c : t₁ ⟷₁^ t₂} → (id⟷₁^ ◎^ c) ⟷₂^ c
  idl◎r^   : {c : t₁ ⟷₁^ t₂} → c ⟷₂^ id⟷₁^ ◎^ c
  idr◎l^   : {c : t₁ ⟷₁^ t₂} → (c ◎^ id⟷₁^) ⟷₂^ c
  idr◎r^   : {c : t₁ ⟷₁^ t₂} → c ⟷₂^ (c ◎^ id⟷₁^)
  linv◎l^  : {c : t₁ ⟷₁^ t₂} → (c ◎^ !⟷₁^ c) ⟷₂^ id⟷₁^
  linv◎r^  : {c : t₁ ⟷₁^ t₂} → id⟷₁^ ⟷₂^ (c ◎^ !⟷₁^ c)
  rinv◎l^  : {c : t₁ ⟷₁^ t₂} → (!⟷₁^ c ◎^ c) ⟷₂^ id⟷₁^
  rinv◎r^  : {c : t₁ ⟷₁^ t₂} → id⟷₁^ ⟷₂^ (!⟷₁^ c ◎^ c)
  -- unite₊l⟷₂l^ : {c₁ : O ⟷₁^ O} {c₂ : t₁ ⟷₁^ t₂} →
  --         (unite₊l ◎^ c₂) ⟷₂^ ((c₁ ⊕ c₂) ◎^ unite₊l)
  -- unite₊l⟷₂r^ : {c₁ : O ⟷₁^ O} {c₂ : t₁ ⟷₁^ t₂} →
  --         ((c₁ ⊕ c₂) ◎^ unite₊l) ⟷₂^ (unite₊l ◎^ c₂)
  -- uniti₊l⟷₂l^ : {c₁ : O ⟷₁^ O} {c₂ : t₁ ⟷₁^ t₂} →
  --         (uniti₊l ◎^ (c₁ ⊕ c₂)) ⟷₂^ (c₂ ◎^ uniti₊l)
  -- uniti₊l⟷₂r^ : {c₁ : O ⟷₁^ O} {c₂ : t₁ ⟷₁^ t₂} →
  --         (c₂ ◎^ uniti₊l) ⟷₂^ (uniti₊l ◎^ (c₁ ⊕ c₂))
  -- swapl₊⟷₂^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₃ ⟷₁^ t₄} →
  --         (swap₊ ◎^ (c₁ ⊕ c₂)) ⟷₂^ ((c₂ ⊕ c₁) ◎^ swap₊)
  -- swapr₊⟷₂^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₃ ⟷₁^ t₄} →
  --         ((c₂ ⊕ c₁) ◎^ swap₊) ⟷₂^ (swap₊ ◎^ (c₁ ⊕ c₂))
  id⟷₂^     : {c : t₁ ⟷₁^ t₂} → c ⟷₂^ c
  trans⟷₂^ : {c₁ c₂ c₃ : t₁ ⟷₁^ t₂} →
         (c₁ ⟷₂^ c₂) → (c₂ ⟷₂^ c₃) → (c₁ ⟷₂^ c₃)
  _⊡^_ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₂ ⟷₁^ t₃} {c₃ : t₁ ⟷₁^ t₂} {c₄ : t₂ ⟷₁^ t₃} →
         (c₁ ⟷₂^ c₃) → (c₂ ⟷₂^ c₄) → (c₁ ◎^ c₂) ⟷₂^ (c₃ ◎^ c₄)
  -- split⊕-id⟷₁^ : (id⟷₁^ {t = t₁ + t₂}) ⟷₂^ (id⟷₁^ ⊕ id⟷₁)

  -- associativity triangle
  -- triangle₊l :
  --   (unite₊r {t = t₁} ⊕ id⟷₁^ {t = t₂}) ⟷₂^ assocr₊ ◎^ (id⟷₁^ ⊕ unite₊l)
  -- triangle₊r :
  --   assocr₊ ◎^ (id⟷₁^ {t = t₁} ⊕ unite₊l {t = t₂}) ⟷₂^ unite₊r ⊕ id⟷₁
  -- pentagon₊l :
  --   assocr₊ ◎^ (assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃ + t₄}) ⟷₂
  --   ((assocr₊ ⊕ id⟷₁) ◎^ assocr₊) ◎^ (id⟷₁^ ⊕ assocr₊)
  -- pentagon₊r :
  --   ((assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃} ⊕ id⟷₁^ {t = t₄}) ◎^ assocr₊) ◎^ (id⟷₁^ ⊕ assocr₊) ⟷₂
  --   assocr₊ ◎^ assocr₊
--   -- unit coherence
  -- unite₊l-coh-l : unite₊l {t = t₁} ⟷₂^ swap₊ ◎^ unite₊r
  -- unite₊l-coh-r : swap₊ ◎^ unite₊r ⟷₂^ unite₊l {t = t₁}
  -- hexagonr₊l :
  --   (assocr₊ ◎^ swap₊) ◎^ assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃} ⟷₂
  --   ((swap₊ ⊕ id⟷₁) ◎^ assocr₊) ◎^ (id⟷₁^ ⊕ swap₊)
  -- hexagonr₊r :
  --   ((swap₊ ⊕ id⟷₁) ◎^ assocr₊) ◎^ (id⟷₁^ ⊕ swap₊) ⟷₂
  --   (assocr₊ ◎^ swap₊) ◎^ assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}
  -- hexagonl₊l :
  --   (assocl₊ ◎^ swap₊) ◎^ assocl₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃} ⟷₂
  --   ((id⟷₁^ ⊕ swap₊) ◎^ assocl₊) ◎^ (swap₊ ⊕ id⟷₁)
  -- hexagonl₊r :
  --   ((id⟷₁^ ⊕ swap₊) ◎^ assocl₊) ◎^ (swap₊ ⊕ id⟷₁) ⟷₂
  --   (assocl₊ ◎^ swap₊) ◎^ assocl₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}
  -- Braiding compatible with unitors (redundant; provable from above
  -- axioms. See for example Thm. 10 in "On MacLane's Conditions for
  -- Coherence of Natural Associativities, Commutativities, etc.
  -- Kelly 1964)
  -- unit-braid : unite₊l {O} ⟷₂^ swap₊ ◎^ unite₊l
  -- braid-unit : swap₊ ◎^ unite₊l ⟷₂^ unite₊l {O}
  
  -- New ones
  ⊕id⟷₁⟷₂^ : ⊕^ id⟷₁^ {n =  n} ⟷₂^ id⟷₁^ {n =  (S n)}
  !⊕id⟷₁⟷₂^ : id⟷₁^ {n =  (S n)} ⟷₂^ ⊕^ id⟷₁^ {n =  n}
  hom◎⊕⟷₂^ : {c₁ : (n) ⟷₁^ (m)} {c₂ : (m) ⟷₁^ (o)} → 
         ((⊕^ c₁) ◎^ (⊕^ c₂)) ⟷₂^ ⊕^ (c₁ ◎^ c₂)
  resp⊕⟷₂  :
         {c₁ : (n) ⟷₁^ (m)} {c₂ : (n) ⟷₁^ (m)} → (c₁ ⟷₂^ c₂) → (⊕^ c₁) ⟷₂^ (⊕^ c₂)
  hom⊕◎⟷₂^ : {c₁ : (n) ⟷₁^ (m)} {c₂ : (m) ⟷₁^ (o)} → 
         ⊕^ (c₁ ◎^ c₂) ⟷₂^ ((⊕^ c₁) ◎^ (⊕^ c₂))

  swapr₊⟷₂^ : {c : (n) ⟷₁^ (n)} 
    → (⊕^ (⊕^ c)) ◎^ swap₊^ ⟷₂^ swap₊^ ◎^ (⊕^ (⊕^ c))
  swapl₊⟷₂^ : {c : (n) ⟷₁^ (n)} 
    → swap₊^ ◎^ (⊕^ (⊕^ c)) ⟷₂^ (⊕^ (⊕^ c)) ◎^ swap₊^

-- -- -- Equational reasoning

infixr 10 _⟷₂^⟨_⟩_
infix  15 _⟷₂^∎

_⟷₂^⟨_⟩_ : ∀ (c₁ : t₁ ⟷₁^ t₂) {c₂ c₃ : t₁ ⟷₁^ t₂} →
         (c₁ ⟷₂^ c₂) → (c₂ ⟷₂^ c₃) → (c₁ ⟷₂^ c₃)
_ ⟷₂^⟨ β ⟩ γ = trans⟷₂^ β γ

_⟷₂^∎ : ∀ (c : t₁ ⟷₁^ t₂) → c ⟷₂^ c
_ ⟷₂^∎ = id⟷₂^

!⟷₂^ : {c₁ c₂ : t₁ ⟷₁^ t₂} → (α : c₁ ⟷₂^ c₂) → (c₂ ⟷₂^ c₁)
!⟷₂^ assoc◎l^ = assoc◎r^
!⟷₂^ assoc◎r^ = assoc◎l^
!⟷₂^ idl◎l^ = idl◎r^
!⟷₂^ idl◎r^ = idl◎l^
!⟷₂^ idr◎l^ = idr◎r^
!⟷₂^ idr◎r^ = idr◎l^
!⟷₂^ linv◎l^ = linv◎r^
!⟷₂^ linv◎r^ = linv◎l^
!⟷₂^ rinv◎l^ = rinv◎r^
!⟷₂^ rinv◎r^ = rinv◎l^
!⟷₂^ id⟷₂^ = id⟷₂^
!⟷₂^ (trans⟷₂^ α α₁) = trans⟷₂^ (!⟷₂^ α₁) (!⟷₂^ α)
!⟷₂^ (α ⊡^ α₁) = !⟷₂^ α ⊡^ !⟷₂^ α₁
!⟷₂^ ⊕id⟷₁⟷₂^ = !⊕id⟷₁⟷₂^
!⟷₂^ !⊕id⟷₁⟷₂^ = ⊕id⟷₁⟷₂^
!⟷₂^ hom◎⊕⟷₂^ = hom⊕◎⟷₂^
!⟷₂^ (resp⊕⟷₂ α) = resp⊕⟷₂ (!⟷₂^ α)
!⟷₂^ hom⊕◎⟷₂^ = hom◎⊕⟷₂^
!⟷₂^ swapl₊⟷₂^ = swapr₊⟷₂^
!⟷₂^ swapr₊⟷₂^ = swapl₊⟷₂^

c₊⟷₂id⟷₁ : (c : (O) ⟷₁^ (O)) → c ⟷₂^ id⟷₁^
c₊⟷₂id⟷₁ id⟷₁^ = id⟷₂^
c₊⟷₂id⟷₁ (_◎^_ {m = (O)} c₁ c₂) = trans⟷₂^ (c₊⟷₂id⟷₁ c₁ ⊡^ c₊⟷₂id⟷₁ c₂) idl◎l^
c₊⟷₂id⟷₁ (_◎^_ {m = ((S m))} c₁ c₂) with (⟷₁^-eq-size c₂)
... | ()

⊕⊕id⟷₁⟷₂^ : {n : ℕ} → (⊕^ ⊕^ id⟷₁^ {n = n}) ⟷₂^ id⟷₁^ {n = S (S n)}
⊕⊕id⟷₁⟷₂^ = trans⟷₂^ (resp⊕⟷₂ ⊕id⟷₁⟷₂^) ⊕id⟷₁⟷₂^

-- -- -- 3-combinators trivial

data _⟷₃^_ :{p q : n ⟷₁^ m} → (p ⟷₂^ q) → (p ⟷₂^ q) → Set where
  trunc : {p q : n ⟷₁^ m} (α β : p ⟷₂^ q) → α ⟷₃^ β
