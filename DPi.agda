{-# OPTIONS --without-K #-}

-- Dependent Pi; want Σ and Π types

module DPi where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Nat hiding (_≟_)
open import Data.List
open import Relation.Nullary
open import Relation.Binary
open import Function
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

inj₁lem : {A B : Set} {x y : A} → _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y) → x ≡ y
inj₁lem refl = refl

_≟_ : {A : U} → Decidable {A = El A} _≡_
_≟_ {ZERO} ()
_≟_ {ONE} tt tt = yes refl
_≟_ {PLUS A B} (inj₁ x) (inj₁ y) with _≟_ {A} x y
_≟_ {PLUS A B} (inj₁ x) (inj₁ .x) | yes refl = yes refl
... | no ¬p = no (¬p ∘ inj₁lem)
_≟_ {PLUS A B} (inj₁ x) (inj₂ y) = {!!}
_≟_ {PLUS A B} (inj₂ x) (inj₁ y) = {!!}
_≟_ {PLUS A B} (inj₂ x) (inj₂ y) = {!!}
_≟_ {TIMES A B} (x , y) (z , w) with _≟_ {A} x z | _≟_ {B} y w
_≟_ {TIMES A B} (x , y) (.x , .y) | yes refl | yes refl = yes refl
_≟_ {TIMES A B} (x , y) (z , w) | no ¬p | yes p = {!!}
_≟_ {TIMES A B} (x , y) (z , w) | yes p | no ¬p = {!!}
_≟_ {TIMES A B} (x , y) (z , w) | no ¬p | no ¬q = {!!}
_≟_ {SIGMA A P} a b = {!!}
_≟_ {PI A P} a b = {!!}
_≟_ {EQ a b} c d = {!!}

-- Questions:
-- Should enum and ∣_∣ map to a flat result or a family of results indexed by a value?

-- Enum: can tighten to a Vector later

enum : (A : U) → List (El A)
enum ZERO = []
enum ONE = tt ∷ []
enum (PLUS A B) = map inj₁ (enum A) ++ map inj₂ (enum B)
enum (TIMES A B) = concat (map (λ b → map (λ a → (a , b)) (enum A)) (enum B))
enum (SIGMA A P) = {!!} -- concat (map (λ a → enum (P a)) (enum A))
enum (PI A P) = {!!}
enum (EQ {A} a b) with _≟_ {A} a b
enum (EQ a .a) | yes refl = refl ∷ []
... | no _ = []

-- Size

∣_∣ : U → ℕ
∣ ZERO ∣ = 0
∣ ONE ∣ = 1
∣ PLUS A B ∣ = ∣ A ∣ + ∣ B ∣
∣ TIMES A B ∣ = ∣ A ∣ * ∣ B ∣
∣ SIGMA A P ∣ = sum (map (λ a → ∣ P a ∣) (enum A))
∣ PI A P ∣ = {!!}
∣ EQ {A} a b ∣ with _≟_ {A} a b
... | yes _ = 1
... | no _ = 0

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

-- Lose TIMES but first make sure that all isomorphisms involving TIMES can be
-- expressed with SIGMA

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
