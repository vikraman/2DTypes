{-# OPTIONS --without-K #-}

module FW where

open import Data.Bool using (Bool; not)
open import Function using (id) renaming (_∘′_ to _○_)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------------
-- Everything is standard: functions, homotopies, equivalences, etc, etc.  The
-- only thing new is identity types and a generalized induction principle J for
-- them. We define a small universe that has just the new concepts and inherit
-- everything else from the ambient Agda environment.

data U : Set
data _⟷_ : U → U → Set

data U where
  `𝟚 : U
  Path : {A B : U} → (A ⟷ B) → U

data _⟷_ where
  `id : {A : U} → A ⟷ A
  `not : `𝟚 ⟷ `𝟚

-- Interpretation

_∼_ : {A B : Set} → (f g : A → B) → Set
_∼_ {A} f g = (a : A) → f a ≡ g a

record isequiv {A B : Set} (f : A → B) : Set where
  constructor mkisequiv
  field
    g : B → A
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

El : U → Set
El `𝟚 = Bool
El (Path {A} `id) = isequiv {El A} id
El (Path `not) = isequiv not

------------------------------------------------------------------------------
-- induction principle (J generalized)

pathInd : ∀ {ℓ} →
          (C : {A B : U} → A ⟷ B → Set ℓ) →
          (cid : {A : U} → C (`id {A})) → (cnot : C `not) →
          ({A B : U} (p : A ⟷ B) → C p)
pathInd C cid cnot `id = cid
pathInd C cid cnot `not = cnot

-- Lemma 2.1.1

_⁻¹ : {A B : U} → (A ⟷ B) → (B ⟷ A)
_⁻¹ = pathInd
        (λ {A} {B} _ → B ⟷ A)
        `id
        `not

-- Will use pattern-matching instead of the explicit induction principle in the
-- following

! : {A B : U} → (A ⟷ B) → (B ⟷ A)
! `id = `id
! `not = `not

-- Lemma 2.1.2
_∘_ : {A B C : U} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)
`id ∘ `id = `id
`id ∘ `not = `not
`not ∘ `id = `not
`not ∘ `not = `id

-- Lemma 2.1.4

-- p = p . refl

unitTransR : {A B : U} → (p : A ⟷ B) → (Path p ⟷ Path (p ∘ `id))
unitTransR `id = `id
unitTransR `not = `id

-- p = refl . p

unitTransL : {A B : U} → (p : A ⟷ B) → (Path p ⟷ Path (`id ∘ p))
unitTransL `id = `id
unitTransL `not = `id


-- ! p . p = refl

invTransL : {A B : U} → (p : A ⟷ B) → (Path (! p ∘ p) ⟷ Path (`id {B}))
invTransL `id = `id
invTransL `not = `id

-- p . ! p = refl

invTransR : {A B : U} → (p : A ⟷ B) → (Path (p ∘ ! p) ⟷ Path (`id {A}))
invTransR `id = `id
invTransR `not = `id

-- ! (! p) = p

invId : {A B : U} → (p : A ⟷ B) → (Path (! (! p)) ⟷ Path p)
invId `id = `id
invId `not = `id

-- p . (q . r) = (p . q) . r

assocP : {A B C D : U} → (p : A ⟷ B) → (q : B ⟷ C) → (r : C ⟷ D) →
         (Path (p ∘ (q ∘ r)) ⟷ Path ((p ∘ q) ∘ r))
assocP `id `id `id = `id
assocP `id `id `not = `id
assocP `id `not `id = `id
assocP `id `not `not = `id
assocP `not `id `id = `id
assocP `not `id `not = `id
assocP `not `not `id = `id
assocP `not `not `not = `id

-- ! (p ∘ q) ≡ ! q ∘ ! p

invComp : {A B C : U} → (p : A ⟷ B) → (q : B ⟷ C) →
          Path (! (p ∘ q)) ⟷ Path (! q ∘ ! p)
invComp `id `id = `id
invComp `id `not = `id
invComp `not `id = `id
invComp `not `not = `id

-- Lemma 2.2.1
-- computation rule: ap f (refl x) = refl (f x)

ap : {A B : U} → (f : U → U) → (A ⟷ B) → (f A ⟷ f B)
ap {A} {.A} f `id = `id
ap {`𝟚} {`𝟚} f `not with f `𝟚
... | `𝟚 = `not
... | Path `id = `id
... | Path `not = `id

-- Lemma 2.2.2

apfTrans : {A B C : U} →
  (f : U → U) → (p : A ⟷ B) → (q : B ⟷ C) →
  Path (ap f (p ∘ q)) ⟷ Path ((ap f p) ∘ (ap f q))
apfTrans f `id `id = `id
apfTrans f `id `not = unitTransL (ap f `not)
apfTrans f `not `id = unitTransR (ap f `not)
apfTrans f `not `not with f `𝟚
... | `𝟚 = ! (invTransL `not)
... | Path `id = `id
... | Path `not = `id

-- transport

transport : {A B : U} → (P : U → U) → (p : A ⟷ B) → El (P A) → El (P B)
transport P `id = id
transport P `not with P `𝟚
... | `𝟚 = not
... | Path `id = id
... | Path `not = id

-- Dependent ap

--apd : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : A → Set ℓ'} {x y : A} → (f : (a : A) → B a) →
--  (p : x ≡ y) → (transport B p (f x) ≡ f y)
--apd : {A B : U} {P : U → U} → (f : (u : U) → El (P u)) →
--  (p : x ⟷ y) → (Path (transport P p (f x)) ⟷ Path (f y))
--apd = {!!}
