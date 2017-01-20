{-# OPTIONS --without-K #-}

module FW where

open import Data.Bool
open import Data.Product
open import Function hiding (_∘_) renaming (_∘′_ to _○_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Courtesy of Wolfram Kahl, a dependent cong₂

cong₂D! : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
         (f : (x : A) → B x → C)
       → {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
       → (x₂≡x₁ : x₂ ≡ x₁) → subst B x₂≡x₁ y₂ ≡ y₁ → f x₁ y₁ ≡ f x₂ y₂
cong₂D! f refl refl = refl

------------------------------------------------------------------------------
-- Everything is standard: functions, homotopies, equivalences, etc, etc.  The
-- only thing new is identity types and a generalized induction principle J for
-- them. We define a small universe that focuses on the new concepts specialized
-- for Bool and inherit everything else from the ambient Agda environment.

-- To be pendantic, we should name this `U as `U1 and we should have `𝟚 : `U0 :
-- `U1 but we omit the uninteresting `U0 from the picture

data `U : Set
data 𝟚⟷𝟚 : Set

data `U where
  `𝟚 : `U
  1-Paths : `U -- 𝟚⟷𝟚
  2-Paths : (c₁ c₂ : 𝟚⟷𝟚) → `U

𝟚 : Set
𝟚 = Bool

data 𝟚⟷𝟚 where
  `id : 𝟚⟷𝟚
  `not : 𝟚⟷𝟚

data _⇔_ : (c₁ c₂ : 𝟚⟷𝟚) → Set where
  `id2 : {c : 𝟚⟷𝟚} → c ⇔ c

El : `U → Set
El `𝟚 = 𝟚
El 1-Paths = 𝟚⟷𝟚
El (2-Paths c₁ c₂) = c₁ ⇔ c₂

-- induction principle (J generalized)

1pathInd : ∀ {ℓ} → (C : (𝟚⟷𝟚) → Set ℓ) →
          (cid : C `id) → (cnot : C `not) →
          (p : 𝟚⟷𝟚) → C p
1pathInd C cid cnot `id = cid
1pathInd C cid cnot `not = cnot

-- Lemma 2.1.1

_⁻¹ : 𝟚⟷𝟚 → 𝟚⟷𝟚
_⁻¹ = 1pathInd (λ _ → 𝟚⟷𝟚) `id `not

-- Will use pattern-matching instead of the explicit induction principle in the
-- following

! : 𝟚⟷𝟚 → 𝟚⟷𝟚
! `id = `id
! `not = `not

-- Lemma 2.1.2
_∘_ : 𝟚⟷𝟚 → 𝟚⟷𝟚 → 𝟚⟷𝟚
`id ∘ `id = `id
`id ∘ `not = `not
`not ∘ `id = `not
`not ∘ `not = `id

-- Lemma 2.1.4

-- p = p . refl

unitTransR : (p : 𝟚⟷𝟚) → p ⇔ (p ∘ `id)
unitTransR `id = `id2
unitTransR `not = `id2

-- p = refl . p

unitTransL : (p : 𝟚⟷𝟚) → p ⇔ (`id ∘ p)
unitTransL `id = `id2
unitTransL `not = `id2

-- ! p . p = refl

invTransL : (p : 𝟚⟷𝟚) → (! p ∘ p) ⇔ `id
invTransL `id = `id2
invTransL `not = `id2

-- p . ! p = refl

invTransR : (p : 𝟚⟷𝟚) → (p ∘ ! p) ⇔ `id
invTransR `id = `id2
invTransR `not = `id2

-- ! (! p) = p

invId : (p : 𝟚⟷𝟚) → ! (! p) ⇔ p
invId `id = `id2
invId `not = `id2

-- p . (q . r) = (p . q) . r

assocP : (p q r : 𝟚⟷𝟚) → (p ∘ (q ∘ r)) ⇔ ((p ∘ q) ∘ r)
assocP `id `id `id = `id2
assocP `id `id `not = `id2
assocP `id `not `id = `id2
assocP `id `not `not = `id2
assocP `not `id `id = `id2
assocP `not `id `not = `id2
assocP `not `not `id = `id2
assocP `not `not `not = `id2

-- ! (p ∘ q) ≡ ! q ∘ ! p

invComp : (p q : 𝟚⟷𝟚) → (! (p ∘ q)) ⇔ (! q ∘ ! p)
invComp `id `id = `id2
invComp `id `not = `id2
invComp `not `id = `id2
invComp `not `not = `id2

-- Looks like ap, apd, transport are all vacuous in our case...

------------------------------------------------------------------------------
-- Univalence

-- Interpretation

_∼_ : {A B : Set} → (f g : A → B) → Set
_∼_ {A} f g = (a : A) → f a ≡ g a

record isequiv {A B : Set} (f : A → B) : Set where
  constructor mkisequiv
  field
    g : B → A
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

_≅_ : Set → Set → Set
A ≅ B = Σ[ f ∈ (A → B) ] isequiv f

pathtoequiv : 𝟚⟷𝟚 → 𝟚 ≅ 𝟚
pathtoequiv `id =
  id , mkisequiv id (λ _ → refl) (λ _ → refl)
pathtoequiv `not =
  not , mkisequiv not
          (λ { false → refl ; true → refl })
          (λ { false → refl ; true → refl })

equivtopath : 𝟚 ≅ 𝟚 → 𝟚⟷𝟚
equivtopath (f , mkisequiv g α β) =
  case f true of (λ { false → `not ; true → `id })

postulate
  funext : {f g : Bool → Bool} → (f ∼ g) → (f ≡ g)

univalence : (𝟚⟷𝟚) ≅ (𝟚 ≅ 𝟚)
univalence = pathtoequiv , mkisequiv equivtopath α β
  where β :  (equivtopath ○ pathtoequiv) ∼ id
        β `id = refl
        β `not = refl

        α : (pathtoequiv ○ equivtopath) ∼ id
        α (f , mkisequiv g h₁ h₂) with equivtopath (f , mkisequiv g h₁ h₂)
        ... | `id = cong₂D! _,_ (funext {!!}) {!!}
        ... | `not = cong₂D! _,_ (funext {!!}) {!!}

{--
------------------------------------------------------------------------------
-- Lemma 2.2.1
-- computation rule: ap f (refl x) = refl (f x)

-- vacuous in our case: there is only function in U → U; it maps Bool to itself

-- Lemma 2.2.2

apfTrans : {A B C : U} →
  (f : U → U) → (p : A ⟷ B) → (q : B ⟷ C) →
  Paths (ap f (p ∘ q)) ⟷ Paths ((ap f p) ∘ (ap f q))
apfTrans f `id `id = `id
apfTrans f `id `not = unitTransL (ap f `not)
apfTrans f `not `id = unitTransR (ap f `not)
apfTrans f `not `not with f `𝟚
... | `𝟚 = ! (invTransL `not)
... | Paths `id = `id
... | Paths `not = `id

-- transport

--transport : {A B : U} → (P : U → U) → (p : A ⟷ B) → El (P A) → El (P B)
--transport P `id = id
--transport P `not with P `𝟚
--... | `𝟚 = not
--... | Paths `id = id
--... | Paths `not = id

-- Dependent ap

--apd : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : A → Set ℓ'} {x y : A} → (f : (a : A) → B a) →
--  (p : x ≡ y) → (transport B p (f x) ≡ f y)
--apd : {A B : U} {P : U → U} → (f : (u : U) → El (P u)) →
--  (p : x ⟷ y) → (Paths (transport P p (f x)) ⟷ Paths (f y))
--apd = {!!}

-- Level 2 induction principle

2pathInd : ∀ {ℓ} {c₁ c₂ : 𝟚⟷𝟚} → (C : c₁ ⇔ c₂ → Set ℓ) →
          (cid2 : C `id2) → (cnotinv : C `notinv) →
          (p : [𝟚⟷𝟚]⇔[𝟚⟷𝟚]) → C p
2pathInd C cid2 cnotinv `id2 = cid2
2pathInd C cid2 cnotinv `notinv = cnotinv

------------------------------------------------------------------------------
--}
