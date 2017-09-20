module PiFin.Syntax where

open import NaturalNumbers using (ℕ; recℕ)

-- The Pi universe is the finite type semiring up-to isomorphism
data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

-- Given n, this returns PLUS ONE (PLUS ONE (... ZERO ...)) n times
-- That is, the "canonical" type with n canonical inhabitants
fromSize : ℕ → U
fromSize = recℕ U ZERO (λ _ → PLUS ONE)

infix  30 _⟷_
infixr 50 _◎_

-- Level 1 Programs: Isomorphisms
-- Notice that we elide all syntactic inverses by having
-- inversion as a primitive combinator
data _⟷_ : U → U → Set where
  unite₊l : {t : U} → PLUS ZERO t ⟷ t
  --uniti₊l : {t : U} → t ⟷ PLUS ZERO t
  --unite₊r : {t : U} → PLUS t ZERO ⟷ t
  --uniti₊r : {t : U} → t ⟷ PLUS t ZERO
  swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  --assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆l  : {t : U} → TIMES ONE t ⟷ t
  --uniti⋆l  : {t : U} → t ⟷ TIMES ONE t
  --unite⋆r : {t : U} → TIMES t ONE ⟷ t
  --uniti⋆r : {t : U} → t ⟷ TIMES t ONE
  swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  --assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  absorbr : {t : U} → TIMES ZERO t ⟷ ZERO
  --absorbl : {t : U} → TIMES t ZERO ⟷ ZERO
  --factorzr : {t : U} → ZERO ⟷ TIMES t ZERO
  --factorzl : {t : U} → ZERO ⟷ TIMES ZERO t
  dist    : {t₁ t₂ t₃ : U} → TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)
  --factor  : {t₁ t₂ t₃ : U} →
  --          PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  --distl   : {t₁ t₂ t₃ : U} → TIMES t₁ (PLUS t₂ t₃) ⟷ PLUS (TIMES t₁ t₂) (TIMES t₁ t₃)
  --factorl : {t₁ t₂ t₃ : U } →
  --          PLUS (TIMES t₁ t₂) (TIMES t₁ t₃) ⟷ TIMES t₁ (PLUS t₂ t₃)
  id⟷    : {t : U} → t ⟷ t
  !        : {t₁ t₂ : U} → t₁ ⟷ t₂ → t₂ ⟷ t₁
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} →
              (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : U} →
              (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)

uniti₊l : {t : U} → t ⟷ PLUS ZERO t
uniti₊l = ! unite₊l

--id⟷ : {t : U} → t ⟷ t
--id⟷ = uniti₊l ◎ unite₊l

assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
assocr₊ = ! assocl₊

assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
assocr⋆ = ! assocl⋆

infix  30 _⇔_

-- Level 2 Programs: Coherences/proofs that two isomorphisms are equal
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
  assocl*l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆) ⇔ (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃))
  assocl*r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃)) ⇔ ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆)
  assocr₊r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⇔ (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃)))
  assocr*l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
           (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃))) ⇔ (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆)
  assocr*r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆) ⇔ (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃)))
  assocr₊l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
           (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))) ⇔ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
  dist⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
          ((a ⊕ b) ⊗ c) ◎ dist ⇔ dist ◎ ((a ⊗ c) ⊕ (b ⊗ c))
  dist⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
          dist ◎ ((a ⊗ c) ⊕ (b ⊗ c)) ⇔ ((a ⊕ b) ⊗ c) ◎ dist
  -- distl⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
  --         {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
  --     (a ⊗ (b ⊕ c)) ◎ distl ⇔ distl ◎ ((a ⊗ b) ⊕ (a ⊗ c))
  -- distl⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
  --         {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
  --     distl ◎ ((a ⊗ b) ⊕ (a ⊗ c)) ⇔ (a ⊗ (b ⊕ c)) ◎ distl
  -- factor⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
  --         {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
  --      ((a ⊗ c) ⊕ (b ⊗ c)) ◎ factor ⇔ factor ◎ ((a ⊕ b) ⊗ c)
  -- factor⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
  --         {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
  --      factor ◎ ((a ⊕ b) ⊗ c) ⇔ ((a ⊗ c) ⊕ (b ⊗ c)) ◎ factor
  -- factorl⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
  --         {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
  --      ((a ⊗ b) ⊕ (a ⊗ c)) ◎ factorl ⇔ factorl ◎ (a ⊗ (b ⊕ c))
  -- factorl⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
  --         {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
  --      factorl ◎ (a ⊗ (b ⊕ c)) ⇔ ((a ⊗ b) ⊕ (a ⊗ c)) ◎ factorl
  idl◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (id⟷ ◎ c) ⇔ c
  idl◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ id⟷ ◎ c
  idr◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ id⟷) ⇔ c
  idr◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ (c ◎ id⟷)
  linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ ! c) ⇔ id⟷
  linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (c ◎ ! c)
  rinv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (! c ◎ c) ⇔ id⟷
  rinv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (! c ◎ c)
  unite₊l⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
          (unite₊l ◎ c₂) ⇔ ((c₁ ⊕ c₂) ◎ unite₊l)
  unite₊l⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
          ((c₁ ⊕ c₂) ◎ unite₊l) ⇔ (unite₊l ◎ c₂)
  uniti₊l⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
          (uniti₊l ◎ (c₁ ⊕ c₂)) ⇔ (c₂ ◎ uniti₊l)
  uniti₊l⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
          (c₂ ◎ uniti₊l) ⇔ (uniti₊l ◎ (c₁ ⊕ c₂))
  -- unite₊r⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
  --         (unite₊r ◎ c₂) ⇔ ((c₂ ⊕ c₁) ◎ unite₊r)
  -- unite₊r⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
  --         ((c₂ ⊕ c₁) ◎ unite₊r) ⇔ (unite₊r ◎ c₂)
  -- uniti₊r⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
  --         (uniti₊r ◎ (c₂ ⊕ c₁)) ⇔ (c₂ ◎ uniti₊r)
  -- uniti₊r⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
  --         (c₂ ◎ uniti₊r) ⇔ (uniti₊r ◎ (c₂ ⊕ c₁))
  swapl₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} →
          (swap₊ ◎ (c₁ ⊕ c₂)) ⇔ ((c₂ ⊕ c₁) ◎ swap₊)
  swapr₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} →
          ((c₂ ⊕ c₁) ◎ swap₊) ⇔ (swap₊ ◎ (c₁ ⊕ c₂))
  -- unitel⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
  --         (unite⋆l ◎ c₂) ⇔ ((c₁ ⊗ c₂) ◎ unite⋆l)
  -- uniter⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
  --         ((c₁ ⊗ c₂) ◎ unite⋆l) ⇔ (unite⋆l ◎ c₂)
  -- unitil⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
  --         (uniti⋆l ◎ (c₁ ⊗ c₂)) ⇔ (c₂ ◎ uniti⋆l)
  -- unitir⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
  --         (c₂ ◎ uniti⋆l) ⇔ (uniti⋆l ◎ (c₁ ⊗ c₂))
  -- unitel⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
  --         (unite⋆r ◎ c₂) ⇔ ((c₂ ⊗ c₁) ◎ unite⋆r)
  -- uniter⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
  --         ((c₂ ⊗ c₁) ◎ unite⋆r) ⇔ (unite⋆r ◎ c₂)
  -- unitil⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
  --         (uniti⋆r ◎ (c₂ ⊗ c₁)) ⇔ (c₂ ◎ uniti⋆r)
  -- unitir⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
  --         (c₂ ◎ uniti⋆r) ⇔ (uniti⋆r ◎ (c₂ ⊗ c₁))
  swapl⋆⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} →
          (swap⋆ ◎ (c₁ ⊗ c₂)) ⇔ ((c₂ ⊗ c₁) ◎ swap⋆)
  swapr⋆⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} →
          ((c₂ ⊗ c₁) ◎ swap⋆) ⇔ (swap⋆ ◎ (c₁ ⊗ c₂))
  id⇔     : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ c
  trans⇔  : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} →
         (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊡_  : {t₁ t₂ t₃ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₁ ⟷ t₂} {c₄ : t₂ ⟷ t₃} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  resp⊗⇔  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊗ c₂) ⇔ (c₃ ⊗ c₄)
  -- -- below are the combinators added for the RigCategory structure
  id⟷⊕id⟷⇔ : {t₁ t₂ : U} → (id⟷ {t₁} ⊕ id⟷ {t₂}) ⇔ id⟷
  split⊕-id⟷ : {t₁ t₂ : U} → (id⟷ {PLUS t₁ t₂}) ⇔ (id⟷ ⊕ id⟷)
  hom⊕◎⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⇔ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⇔ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
  id⟷⊗id⟷⇔ : {t₁ t₂ : U} → (id⟷ {t₁} ⊗ id⟷ {t₂}) ⇔ id⟷
  split⊗-id⟷ : {t₁ t₂ : U} → (id⟷ {TIMES t₁ t₂}) ⇔ (id⟷ ⊗ id⟷)
  hom⊗◎⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄)) ⇔ ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄))
  hom◎⊗⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
         ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄)) ⇔ ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄))
  -- -- associativity triangle
  -- triangle⊕l : {t₁ t₂ : U} →
  --   (unite₊r {t₁} ⊕ id⟷ {t₂}) ⇔ assocr₊ ◎ (id⟷ ⊕ unite₊l)
  -- triangle⊕r : {t₁ t₂ : U} →
  --   assocr₊ ◎ (id⟷ {t₁} ⊕ unite₊l {t₂}) ⇔ (unite₊r ⊕ id⟷)
  -- triangle⊗l : {t₁ t₂ : U} →
  --   ((unite⋆r {t₁}) ⊗ id⟷ {t₂}) ⇔ assocr⋆ ◎ (id⟷ ⊗ unite⋆l)
  -- triangle⊗r : {t₁ t₂ : U} →
  --   (assocr⋆ ◎ (id⟷ {t₁} ⊗ unite⋆l {t₂})) ⇔ (unite⋆r ⊗ id⟷)
  -- pentagon⊕l : {t₁ t₂ t₃ t₄ : U} →
  --   assocr₊ ◎ (assocr₊ {t₁} {t₂} {PLUS t₃ t₄}) ⇔
  --   ((assocr₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊)
  -- pentagon⊕r : {t₁ t₂ t₃ t₄ : U} →
  --   ((assocr₊ {t₁} {t₂} {t₃} ⊕ id⟷ {t₄}) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊) ⇔
  --   assocr₊ ◎ assocr₊
  -- pentagon⊗l : {t₁ t₂ t₃ t₄ : U} →
  --   assocr⋆ ◎ (assocr⋆ {t₁} {t₂} {TIMES t₃ t₄}) ⇔
  --   ((assocr⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆)
  -- pentagon⊗r : {t₁ t₂ t₃ t₄ : U} →
  --   ((assocr⋆ {t₁} {t₂} {t₃} ⊗ id⟷ {t₄}) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆) ⇔
  --   assocr⋆ ◎ assocr⋆
  -- -- from the braiding
  -- -- unit coherence
  -- unite₊l-coh-l : {t₁ : U} → unite₊l {t₁} ⇔ swap₊ ◎ unite₊r
  -- unite₊l-coh-r : {t₁ : U} → swap₊ ◎ unite₊r ⇔ unite₊l {t₁}
  -- unite⋆l-coh-l : {t₁ : U} → unite⋆l {t₁} ⇔ swap⋆ ◎ unite⋆r
  -- unite⋆l-coh-r : {t₁ : U} → swap⋆ ◎ unite⋆r ⇔ unite⋆l {t₁}
  -- hexagonr⊕l : {t₁ t₂ t₃ : U} →
  --   (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃} ⇔
  --   ((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊)
  -- hexagonr⊕r : {t₁ t₂ t₃ : U} →
  --   ((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊) ⇔
  --   (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃}
  -- hexagonl⊕l : {t₁ t₂ t₃ : U} →
  --   (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃} ⇔
  --   ((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷)
  -- hexagonl⊕r : {t₁ t₂ t₃ : U} →
  --   ((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷) ⇔
  --   (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃}
  -- hexagonr⊗l : {t₁ t₂ t₃ : U} →
  --   (assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃} ⇔
  --   ((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆)
  -- hexagonr⊗r : {t₁ t₂ t₃ : U} →
  --   ((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆) ⇔
  --   (assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃}
  -- hexagonl⊗l : {t₁ t₂ t₃ : U} →
  --   (assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃} ⇔
  --   ((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷)
  -- hexagonl⊗r : {t₁ t₂ t₃ : U} →
  --   ((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷) ⇔
  --   (assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃}
  -- absorbl⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
  --   (c₁ ⊗ id⟷ {ZERO}) ◎ absorbl ⇔ absorbl ◎ id⟷ {ZERO}
  -- absorbl⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
  --   absorbl ◎ id⟷ {ZERO} ⇔ (c₁ ⊗ id⟷ {ZERO}) ◎ absorbl
  -- absorbr⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
  --   (id⟷ {ZERO} ⊗ c₁) ◎ absorbr ⇔ absorbr ◎ id⟷ {ZERO}
  -- absorbr⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
  --   absorbr ◎ id⟷ {ZERO} ⇔ (id⟷ {ZERO} ⊗ c₁) ◎ absorbr
  -- factorzl⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
  --   id⟷ ◎ factorzl ⇔ factorzl ◎ (id⟷ ⊗ c₁)
  -- factorzl⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
  --   factorzl ◎ (id⟷ {ZERO} ⊗ c₁) ⇔ id⟷ {ZERO} ◎ factorzl
  -- factorzr⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
  --   id⟷ ◎ factorzr ⇔ factorzr ◎ (c₁ ⊗ id⟷)
  -- factorzr⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
  --   factorzr ◎ (c₁ ⊗ id⟷) ⇔ id⟷ ◎ factorzr
  -- -- from the coherence conditions of RigCategory
  -- swap₊distl⇔l : {t₁ t₂ t₃ : U} →
  --   (id⟷ {t₁} ⊗ swap₊ {t₂} {t₃}) ◎ distl ⇔ distl ◎ swap₊
  -- swap₊distl⇔r : {t₁ t₂ t₃ : U} →
  --   distl ◎ swap₊ ⇔ (id⟷ {t₁} ⊗ swap₊ {t₂} {t₃}) ◎ distl
  -- dist-swap⋆⇔l : {t₁ t₂ t₃ : U} →
  --   dist {t₁} {t₂} {t₃} ◎ (swap⋆ ⊕ swap⋆) ⇔ swap⋆ ◎ distl
  -- dist-swap⋆⇔r : {t₁ t₂ t₃ : U} →
  --   swap⋆ ◎ distl {t₁} {t₂} {t₃} ⇔ dist ◎ (swap⋆ ⊕ swap⋆)
  -- assocl₊-dist-dist⇔l : {t₁ t₂ t₃ t₄ : U} →
  --   ((assocl₊ {t₁} {t₂} {t₃} ⊗ id⟷ {t₄}) ◎ dist) ◎ (dist ⊕ id⟷) ⇔
  --   (dist ◎ (id⟷ ⊕ dist)) ◎ assocl₊
  -- assocl₊-dist-dist⇔r : {t₁ t₂ t₃ t₄ : U} →
  --   (dist {t₁} ◎ (id⟷ ⊕ dist {t₂} {t₃} {t₄})) ◎ assocl₊ ⇔
  --   ((assocl₊ ⊗ id⟷) ◎ dist) ◎ (dist ⊕ id⟷)
  -- assocl⋆-distl⇔l : {t₁ t₂ t₃ t₄ : U} →
  --   assocl⋆ {t₁} {t₂} ◎ distl {TIMES t₁ t₂} {t₃} {t₄} ⇔
  --   ((id⟷ ⊗ distl) ◎ distl) ◎ (assocl⋆ ⊕ assocl⋆)
  -- assocl⋆-distl⇔r : {t₁ t₂ t₃ t₄ : U} →
  --   ((id⟷ ⊗ distl) ◎ distl) ◎ (assocl⋆ ⊕ assocl⋆) ⇔
  --   assocl⋆ {t₁} {t₂} ◎ distl {TIMES t₁ t₂} {t₃} {t₄}
  -- absorbr0-absorbl0⇔ : absorbr {ZERO} ⇔ absorbl {ZERO}
  -- absorbl0-absorbr0⇔ : absorbl {ZERO} ⇔ absorbr {ZERO}
  -- absorbr⇔distl-absorb-unite : {t₁ t₂ : U} →
  --   absorbr ⇔ (distl {t₂ = t₁} {t₂} ◎ (absorbr ⊕ absorbr)) ◎ unite₊l
  -- distl-absorb-unite⇔absorbr : {t₁ t₂ : U} →
  --   (distl {t₂ = t₁} {t₂} ◎ (absorbr ⊕ absorbr)) ◎ unite₊l ⇔ absorbr
  -- unite⋆r0-absorbr1⇔ : unite⋆r ⇔ absorbr
  -- absorbr1-unite⋆r-⇔ : absorbr ⇔ unite⋆r
  -- absorbl≡swap⋆◎absorbr : {t₁ : U} → absorbl {t₁} ⇔ swap⋆ ◎ absorbr
  -- swap⋆◎absorbr≡absorbl : {t₁ : U} → swap⋆ ◎ absorbr ⇔ absorbl {t₁}
  -- absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr : {t₁ t₂ : U} →
  --   absorbr ⇔ (assocl⋆ {ZERO} {t₁} {t₂} ◎ (absorbr ⊗ id⟷)) ◎ absorbr
  -- [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr : {t₁ t₂ : U} →
  --   (assocl⋆ {ZERO} {t₁} {t₂} ◎ (absorbr ⊗ id⟷)) ◎ absorbr ⇔ absorbr
  -- [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr : {t₁ t₂ : U} →
  --   (id⟷ ⊗ absorbr {t₂}) ◎ absorbl {t₁} ⇔
  --   (assocl⋆ ◎ (absorbl ⊗ id⟷)) ◎ absorbr
  -- assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl : {t₁ t₂ : U} →
  --   (assocl⋆ ◎ (absorbl ⊗ id⟷)) ◎ absorbr ⇔
  --   (id⟷ ⊗ absorbr {t₂}) ◎ absorbl {t₁}
  -- elim⊥-A[0⊕B]⇔l : {t₁ t₂ : U} →
  --    (id⟷ {t₁} ⊗ unite₊l {t₂}) ⇔
  --    (distl ◎ (absorbl ⊕ id⟷)) ◎ unite₊l
  -- elim⊥-A[0⊕B]⇔r : {t₁ t₂ : U} →
  --    (distl ◎ (absorbl ⊕ id⟷)) ◎ unite₊l ⇔ (id⟷ {t₁} ⊗ unite₊l {t₂})
  -- elim⊥-1[A⊕B]⇔l : {t₁ t₂ : U} →
  --   unite⋆l ⇔
  --   distl ◎ (unite⋆l {t₁} ⊕ unite⋆l {t₂})
  -- elim⊥-1[A⊕B]⇔r : {t₁ t₂ : U} →
  --   distl ◎ (unite⋆l {t₁} ⊕ unite⋆l {t₂}) ⇔ unite⋆l
  -- fully-distribute⇔l : {t₁ t₂ t₃ t₄ : U} →
  --   (distl ◎ (dist {t₁} {t₂} {t₃} ⊕ dist {t₁} {t₂} {t₄})) ◎ assocl₊ ⇔
  --     ((((dist ◎ (distl ⊕ distl)) ◎ assocl₊) ◎ (assocr₊ ⊕ id⟷)) ◎
  --        ((id⟷ ⊕ swap₊) ⊕ id⟷)) ◎ (assocl₊ ⊕ id⟷)
  -- fully-distribute⇔r : {t₁ t₂ t₃ t₄ : U} →
  --   ((((dist ◎ (distl ⊕ distl)) ◎ assocl₊) ◎ (assocr₊ ⊕ id⟷)) ◎
  --      ((id⟷ ⊕ swap₊) ⊕ id⟷)) ◎ (assocl₊ ⊕ id⟷) ⇔
  --   (distl ◎ (dist {t₁} {t₂} {t₃} ⊕ dist {t₁} {t₂} {t₄})) ◎ assocl₊


-- Level 3 is trivial i.e. all coherences are equal
data _⇌_ {X Y : U} {p q : X ⟷ Y} (u v : p ⇔ q) : Set where
  trunc : u ⇌ v
