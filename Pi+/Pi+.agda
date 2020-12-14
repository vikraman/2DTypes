{-# OPTIONS --without-K #-}

module Pi+.Pi+ where

data U : Set where
  O I : U
  _+_ : U → U → U

infixr 40 _+_
infix 30 _⟷₁_
infixr 50 _◎_ _⊕_

data _⟷₁_  : U → U → Set where
  unite₊l : {t : U} → O + t ⟷₁ t
  swap₊   : {t₁ t₂ : U} → t₁ + t₂ ⟷₁ t₂ + t₁
  assocl₊ : {t₁ t₂ t₃ : U} → t₁ + (t₂ + t₃) ⟷₁ (t₁ + t₂) + t₃
  id⟷₁     : {t : U} → t ⟷₁ t
  !⟷₁      : {t₁ t₂ : U} → t₁ ⟷₁ t₂ → t₂ ⟷₁ t₁
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷₁ t₂) → (t₂ ⟷₁ t₃) → (t₁ ⟷₁ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} → (t₁ ⟷₁ t₃) → (t₂ ⟷₁ t₄) → (t₁ + t₂ ⟷₁ t₃ + t₄)

uniti₊l : {t : U} → t ⟷₁ O + t
uniti₊l = !⟷₁ unite₊l

assocr₊ : {t₁ t₂ t₃ : U} → (t₁ + t₂) + t₃ ⟷₁ t₁ + (t₂ + t₃)
assocr₊ = !⟷₁ assocl₊

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

data _⟷₃_ : {X Y : U} {p q : X ⟷₁ Y} → (p ⟷₂ q) → (p ⟷₂ q) → Set where
  trunc : {X Y : U} {p q : X ⟷₁ Y} (α β : p ⟷₂ q) → α ⟷₃ β
