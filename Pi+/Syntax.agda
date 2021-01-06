{-# OPTIONS --without-K #-}

module Pi+.Syntax where

data U : Set where
  O I : U
  _+_ : U → U → U

infixr 40 _+_
infix 30 _⟷₁_
infixr 50 _◎_ _⊕_

data _⟷₁_  : U → U → Set where
  unite₊l : {t : U} → O + t ⟷₁ t
  uniti₊l : {t : U} → t ⟷₁ O + t
  swap₊   : {t₁ t₂ : U} → t₁ + t₂ ⟷₁ t₂ + t₁
  assocl₊ : {t₁ t₂ t₃ : U} → t₁ + (t₂ + t₃) ⟷₁ (t₁ + t₂) + t₃
  assocr₊ : {t₁ t₂ t₃ : U} → (t₁ + t₂) + t₃ ⟷₁ t₁ + (t₂ + t₃)
  id⟷₁     : {t : U} → t ⟷₁ t
--  !⟷₁      : {t₁ t₂ : U} → t₁ ⟷₁ t₂ → t₂ ⟷₁ t₁
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷₁ t₂) → (t₂ ⟷₁ t₃) → (t₁ ⟷₁ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} → (t₁ ⟷₁ t₃) → (t₂ ⟷₁ t₄) → (t₁ + t₂ ⟷₁ t₃ + t₄)

-- uniti₊l : {t : U} → t ⟷₁ O + t
-- uniti₊l = !⟷₁ unite₊l

-- assocr₊ : {t₁ t₂ t₃ : U} → (t₁ + t₂) + t₃ ⟷₁ t₁ + (t₂ + t₃)
-- assocr₊ = !⟷₁ assocl₊

unite₊r : {t : U} → t + O ⟷₁ t
unite₊r = swap₊ ◎ unite₊l

!⟷₁ : {t₁ t₂ : U} → t₁ ⟷₁ t₂ → t₂ ⟷₁ t₁
!⟷₁ unite₊l = uniti₊l
!⟷₁ uniti₊l = unite₊l
!⟷₁ swap₊ = swap₊
!⟷₁ assocl₊ = assocr₊
!⟷₁ assocr₊ = assocl₊
!⟷₁ id⟷₁ = id⟷₁
!⟷₁ (c₁ ◎ c₂) = !⟷₁ c₂ ◎ !⟷₁ c₁
!⟷₁ (c₁ ⊕ c₂) = !⟷₁ c₁ ⊕ !⟷₁ c₂

data _⟷₂_ : {X Y : U} → X ⟷₁ Y → X ⟷₁ Y → Set where
  assoc◎l : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₃ ⟷₁ t₄} →
          (c₁ ◎ (c₂ ◎ c₃)) ⟷₂ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₃ ⟷₁ t₄} →
          ((c₁ ◎ c₂) ◎ c₃) ⟷₂ (c₁ ◎ (c₂ ◎ c₃))
  assocl₊l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊) ⟷₂ (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃))
  assocl₊r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃)) ⟷₂ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊)
  assocr₊r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⟷₂ (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃)))
  assocr₊l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
           (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))) ⟷₂ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
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
  swapl₊⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} →
          (swap₊ ◎ (c₁ ⊕ c₂)) ⟷₂ ((c₂ ⊕ c₁) ◎ swap₊)
  swapr₊⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} →
          ((c₂ ⊕ c₁) ◎ swap₊) ⟷₂ (swap₊ ◎ (c₁ ⊕ c₂))
  id⟷₂     : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → c ⟷₂ c
  trans⟷₂  : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷₁ t₂} →
         (c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₃) → (c₁ ⟷₂ c₃)
  _⊡_  : {t₁ t₂ t₃ : U}
         {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₁ ⟷₁ t₂} {c₄ : t₂ ⟷₁ t₃} →
         (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ◎ c₂) ⟷₂ (c₃ ◎ c₄)
  resp⊕⟷₂  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₁ ⟷₁ t₂} {c₄ : t₃ ⟷₁ t₄} →
         (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ⊕ c₂) ⟷₂ (c₃ ⊕ c₄)
  id⟷₁⊕id⟷₁⟷₂ : {t₁ t₂ : U} → (id⟷₁ {t₁} ⊕ id⟷₁ {t₂}) ⟷₂ id⟷₁
  split⊕-id⟷₁ : {t₁ t₂ : U} → (id⟷₁ {t₁ + t₂}) ⟷₂ (id⟷₁ ⊕ id⟷₁)
  hom⊕◎⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷₁ t₁} {c₂ : t₆ ⟷₁ t₂}
        {c₃ : t₁ ⟷₁ t₃} {c₄ : t₂ ⟷₁ t₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⟷₂ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷₁ t₁} {c₂ : t₆ ⟷₁ t₂}
        {c₃ : t₁ ⟷₁ t₃} {c₄ : t₂ ⟷₁ t₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⟷₂ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
  triangle⊕l : {t₁ t₂ : U} →
    unite₊l ⟷₂ assocl₊ {O} {t₁} {t₂} ◎ (unite₊l ⊕ id⟷₁)
  triangle⊕r : {t₁ t₂ : U} →
    assocl₊ {O} {t₁} {t₂} ◎ (unite₊l ⊕ id⟷₁) ⟷₂ unite₊l

-- Equational reasoning

infixr 10 _⟷₂⟨_⟩_
infix  15 _⟷₂∎

_⟷₂⟨_⟩_ : ∀ {t₁ t₂ : U} (c₁ : t₁ ⟷₁ t₂) {c₂ c₃ : t₁ ⟷₁ t₂} →
         (c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₃) → (c₁ ⟷₂ c₃)
_ ⟷₂⟨ β ⟩ γ = trans⟷₂ β γ

_⟷₂∎ : ∀ {t₁ t₂ : U} (c : t₁ ⟷₁ t₂) → c ⟷₂ c
_ ⟷₂∎ = id⟷₂

!⟷₂ : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷₁ t₂} → (α : c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₁)
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
!⟷₂ triangle⊕l = triangle⊕r
!⟷₂ triangle⊕r = triangle⊕l

{--
!⟷₁⟷₂ : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷₁ t₂} → (α : c₁ ⟷₂ c₂) → (!⟷₁ c₁ ⟷₂ !⟷₁ c₂)
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
!⟷₁⟷₂ (trans⟷₂ α α₁) = trans⟷₂ (!⟷₁⟷₂ α) (!⟷₁⟷₂ α₁)
!⟷₁⟷₂ (α ⊡ α₁) = !⟷₁⟷₂ α₁ ⊡ !⟷₁⟷₂ α
!⟷₁⟷₂ (resp⊕⟷₂ α α₁) = resp⊕⟷₂ (!⟷₁⟷₂ α) (!⟷₁⟷₂ α₁)
!⟷₁⟷₂ id⟷₁⊕id⟷₁⟷₂ = id⟷₁⊕id⟷₁⟷₂
!⟷₁⟷₂ split⊕-id⟷₁ = split⊕-id⟷₁
!⟷₁⟷₂ hom⊕◎⟷₂ = hom⊕◎⟷₂
!⟷₁⟷₂ hom◎⊕⟷₂ = hom◎⊕⟷₂
!⟷₁⟷₂ triangle⊕l = {!!}
!⟷₁⟷₂ triangle⊕r = {!!}
--}

!⟷₁!⟷₁ : {t₁ t₂ : U} → (c : t₁ ⟷₁ t₂) → (!⟷₁ (!⟷₁ c) ⟷₂ c)
!⟷₁!⟷₁ unite₊l = id⟷₂
!⟷₁!⟷₁ uniti₊l = id⟷₂
!⟷₁!⟷₁ swap₊ = id⟷₂
!⟷₁!⟷₁ assocl₊ = id⟷₂
!⟷₁!⟷₁ assocr₊ = id⟷₂
!⟷₁!⟷₁ id⟷₁ = id⟷₂
!⟷₁!⟷₁ (c ◎ c₁) = !⟷₁!⟷₁ c ⊡ !⟷₁!⟷₁ c₁
!⟷₁!⟷₁ (c ⊕ c₁) = resp⊕⟷₂ (!⟷₁!⟷₁ c) (!⟷₁!⟷₁ c₁)

data _⟷₃_ : {X Y : U} {p q : X ⟷₁ Y} → (p ⟷₂ q) → (p ⟷₂ q) → Set where
  trunc : {X Y : U} {p q : X ⟷₁ Y} (α β : p ⟷₂ q) → α ⟷₃ β
