{-# OPTIONS --without-K #-}

-- Dependent Pi; want Σ and Π types

module DPi where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

infix  30 _⟷_
infixr 50 _◎_

------------------------------------------------------------------------------
data U : Set
El : U → Set

data U where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U
  SIGMA : (A : U) → (El A → U) → U
  PI    : (A : U) → (El A → U) → U
  EQ    : {A : U} → (a b : El A) → U

El ZERO        = ⊥
El ONE         = ⊤
El (PLUS A B)  = El A ⊎ El B
El (TIMES A B) = El A × El B
El (SIGMA A P) = Σ[ v ∈ El A ] El (P v)
El (PI A P)    = (v : El A) → El (P v)
El (EQ a b)    = a ≡ b

-- Examples

`𝟚 : U
`𝟚 = PLUS ONE ONE

false true : El `𝟚
false = inj₁ tt
true = inj₂ tt

`A : U
`A = SIGMA `𝟚 (λ b → EQ {`𝟚} b false)

a b : El `A
a = false , refl
b = true , {!!} -- empty

`B : U
`B = PI `𝟚 (λ b → EQ {`𝟚} b false)

c : El `B
c (inj₁ _) = refl
c (inj₂ _) = {!!} -- empty

-- University algebra (Altenkirch)

data _⟷_ : U → U → Set where
  -- All isomorphisms between finite types
  unite₊l : {t : U} → PLUS ZERO t ⟷ t
  uniti₊l : {t : U} → t ⟷ PLUS ZERO t
  unite₊r : {t : U} → PLUS t ZERO ⟷ t
  uniti₊r : {t : U} → t ⟷ PLUS t ZERO
  swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆l  : {t : U} → TIMES ONE t ⟷ t
  uniti⋆l  : {t : U} → t ⟷ TIMES ONE t
  unite⋆r : {t : U} → TIMES t ONE ⟷ t
  uniti⋆r : {t : U} → t ⟷ TIMES t ONE
  swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  absorbr : {t : U} → TIMES ZERO t ⟷ ZERO
  absorbl : {t : U} → TIMES t ZERO ⟷ ZERO
  factorzr : {t : U} → ZERO ⟷ TIMES t ZERO
  factorzl : {t : U} → ZERO ⟷ TIMES ZERO t
  dist    : {t₁ t₂ t₃ : U} →
            TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)
  factor  : {t₁ t₂ t₃ : U} →
            PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  distl   : {t₁ t₂ t₃ : U } →
            TIMES t₁ (PLUS t₂ t₃) ⟷ PLUS (TIMES t₁ t₂) (TIMES t₁ t₃)
  factorl : {t₁ t₂ t₃ : U } →
            PLUS (TIMES t₁ t₂) (TIMES t₁ t₃) ⟷ TIMES t₁ (PLUS t₂ t₃)
  id⟷    : {t : U} → t ⟷ t
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} →
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : U} →
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)
  -- New isomorphisms
  PI1 : {P : ⊤ → U} → PI ONE P ⟷ P tt
  SIGMA1 : {P : ⊤ → U} → SIGMA ONE P ⟷ P tt
  PIPLUS : {A B : U} {P : El A ⊎ El B → U} →
           PI (PLUS A B) P ⟷ TIMES (PI A (λ a → P (inj₁ a)))
                                    (PI B (λ b → (P (inj₂ b))))


------------------------------------------------------------------------------
{--
data U where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U
  SIGMA : (A : U) → (El A → U) → U
  PI    : (A : U) → (El A → U) → U
  EQ    : {A : U} → (a b : El A) → U
--}
