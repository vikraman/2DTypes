{-# OPTIONS --without-K #-}

module Pi+.Pi+ where

data U : Set where
  O I : U
  _+_ : U → U → U

infixr 40 _+_
infix 30 _⟷_
infixr 50 _◎_ _⊕_

data _⟷_  : U → U → Set where
  unite₊l : {t : U} → O + t ⟷ t
  swap₊   : {t₁ t₂ : U} → t₁ + t₂ ⟷ t₂ + t₁
  assocl₊ : {t₁ t₂ t₃ : U} → t₁ + (t₂ + t₃) ⟷ (t₁ + t₂) + t₃
  id⟷     : {t : U} → t ⟷ t
  !⟷      : {t₁ t₂ : U} → t₁ ⟷ t₂ → t₂ ⟷ t₁
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ + t₂ ⟷ t₃ + t₄)

uniti₊l : {t : U} → t ⟷ O + t
uniti₊l = !⟷ unite₊l

assocr₊ : {t₁ t₂ t₃ : U} → (t₁ + t₂) + t₃ ⟷ t₁ + (t₂ + t₃)
assocr₊ = !⟷ assocl₊

data _⇔_ : {X Y : U} → X ⟷ Y → X ⟷ Y → Set where
  assoc◎l : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
          (c₁ ◎ (c₂ ◎ c₃)) ⇔ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
          ((c₁ ◎ c₂) ◎ c₃) ⇔ (c₁ ◎ (c₂ ◎ c₃))
  assocl₊l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊) ⇔ (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃))
  assocl₊r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃)) ⇔ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊)
  assocr₊r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⇔ (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃)))
  assocr₊l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
           (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))) ⇔ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
  idl◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (id⟷ ◎ c) ⇔ c
  idl◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ id⟷ ◎ c
  idr◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ id⟷) ⇔ c
  idr◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ (c ◎ id⟷)
  linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ !⟷ c) ⇔ id⟷
  linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (c ◎ !⟷ c)
  rinv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (!⟷ c ◎ c) ⇔ id⟷
  rinv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (!⟷ c ◎ c)
  unite₊l⇔l : {t₁ t₂ : U} {c₁ : O ⟷ O} {c₂ : t₁ ⟷ t₂} →
          (unite₊l ◎ c₂) ⇔ ((c₁ ⊕ c₂) ◎ unite₊l)
  unite₊l⇔r : {t₁ t₂ : U} {c₁ : O ⟷ O} {c₂ : t₁ ⟷ t₂} →
          ((c₁ ⊕ c₂) ◎ unite₊l) ⇔ (unite₊l ◎ c₂)
  uniti₊l⇔l : {t₁ t₂ : U} {c₁ : O ⟷ O} {c₂ : t₁ ⟷ t₂} →
          (uniti₊l ◎ (c₁ ⊕ c₂)) ⇔ (c₂ ◎ uniti₊l)
  uniti₊l⇔r : {t₁ t₂ : U} {c₁ : O ⟷ O} {c₂ : t₁ ⟷ t₂} →
          (c₂ ◎ uniti₊l) ⇔ (uniti₊l ◎ (c₁ ⊕ c₂))
  swapl₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} →
          (swap₊ ◎ (c₁ ⊕ c₂)) ⇔ ((c₂ ⊕ c₁) ◎ swap₊)
  swapr₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} →
          ((c₂ ⊕ c₁) ◎ swap₊) ⇔ (swap₊ ◎ (c₁ ⊕ c₂))
  id⇔     : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ c
  trans⇔  : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} →
         (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊡_  : {t₁ t₂ t₃ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₁ ⟷ t₂} {c₄ : t₂ ⟷ t₃} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  id⟷⊕id⟷⇔ : {t₁ t₂ : U} → (id⟷ {t₁} ⊕ id⟷ {t₂}) ⇔ id⟷
  split⊕-id⟷ : {t₁ t₂ : U} → (id⟷ {t₁ + t₂}) ⇔ (id⟷ ⊕ id⟷)
  hom⊕◎⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⇔ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⇔ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
