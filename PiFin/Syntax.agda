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

-- Level 2 Programs: Coherences/proofs that two isomorphisms are equal
-- TODO: Finish this definition
data _⇔_ : {X Y : U} → X ⟷ Y → X ⟷ Y → Set where

-- Level 3 is trivial i.e. all coherences are equal
data _⇌_ {X Y : U} {p q : X ⟷ Y} (u v : p ⇔ q) : Set where
  trunc : u ⇌ v
