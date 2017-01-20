{-# OPTIONS --without-K #-}

module FW where

open import Data.Bool using (Bool; not; true; false)
open import Data.Product
open import Function using (id; case_of_) renaming (_∘′_ to _○_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- Everything is standard: functions, homotopies, equivalences, etc, etc.  The
-- only thing new is identity types and a generalized induction principle J for
-- them. We define a small universe that focuses on the new concepts specialized
-- for Bool and inherit everything else from the ambient Agda environment.

data `U : Set
data Bool⟷Bool : Set
data _⇔_ : (Bool⟷Bool) → (Bool⟷Bool) → Set
El : `U → Set

-- Syntax
data `U where
  `𝟚 : `U
  1-Paths : `U
  2-Paths : (c₁ c₂ : El 1-Paths) → `U

-- 1-Paths
data Bool⟷Bool where
  `id : Bool⟷Bool
  `not : Bool⟷Bool
  _•_ : (Bool⟷Bool) → (Bool⟷Bool) → (Bool⟷Bool)

-- 2-Paths
data _⇔_ where
  `id2 : (c : Bool⟷Bool) → (c ⇔ c)
  `notnot : (`not • `not) ⇔ `id

-- Interpretation
El `𝟚 = Bool
El 1-Paths = Bool⟷Bool
El (2-Paths c₁ c₂) = c₁ ⇔ c₂

-- So now we can use the Agda environment remembering to specialize all sets to
-- things in the image of El

------------------------------------------------------------------------------
-- induction principle (J generalized)

xx : ∀ {ℓ} → {C : (Bool⟷Bool) → Set ℓ} {p q : Bool⟷Bool} → C p → C q → C (p • q)
xx a b = {!!}

1pathInd : ∀ {ℓ} → (C : (Bool⟷Bool) → Set ℓ) →
          (cid : C `id) → (cnot : C `not) →
          (p : Bool⟷Bool) → C p
1pathInd C cid cnot `id = cid
1pathInd C cid cnot `not = cnot
1pathInd C cid cnot (p • q) =
  xx {C = C} (1pathInd C cid cnot p) (1pathInd C cid cnot q)

2pathInd : ∀ {ℓ} → (C : {c₁ c₂ : Bool⟷Bool} → c₁ ⇔ c₂ → Set ℓ) →
          (cid : (c : Bool⟷Bool) → C (`id2 c)) → (cnotnot : C `notnot) →
          ({c₁ c₂ : Bool⟷Bool} (p : c₁ ⇔ c₂) → C p)
2pathInd C cid cnotnot (`id2 c) = cid c
2pathInd C cid cnotnot `notnot = cnotnot






{--

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

unitTransR : {A B : U} → (p : A ⟷ B) → (Paths p ⟷ Paths (p ∘ `id))
unitTransR `id = `id
unitTransR `not = `id

-- p = refl . p

unitTransL : {A B : U} → (p : A ⟷ B) → (Paths p ⟷ Paths (`id ∘ p))
unitTransL `id = `id
unitTransL `not = `id


-- ! p . p = refl

invTransL : {A B : U} → (p : A ⟷ B) → (Paths (! p ∘ p) ⟷ Paths (`id {B}))
invTransL `id = `id
invTransL `not = `id

-- p . ! p = refl

invTransR : {A B : U} → (p : A ⟷ B) → (Paths (p ∘ ! p) ⟷ Paths (`id {A}))
invTransR `id = `id
invTransR `not = `id

-- ! (! p) = p

invId : {A B : U} → (p : A ⟷ B) → (Paths (! (! p)) ⟷ Paths p)
invId `id = `id
invId `not = `id

-- p . (q . r) = (p . q) . r

assocP : {A B C D : U} → (p : A ⟷ B) → (q : B ⟷ C) → (r : C ⟷ D) →
         (Paths (p ∘ (q ∘ r)) ⟷ Paths ((p ∘ q) ∘ r))
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
          Paths (! (p ∘ q)) ⟷ Paths (! q ∘ ! p)
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
... | Paths `id = `id
... | Paths `not = `id

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

------------------------------------------------------------------------------
-- Univalence

{--
-- Interpretation

_∼_ : {A B : Set} → (f g : A → B) → Set
_∼_ {A} f g = (a : A) → f a ≡ g a

record isequiv {A B : Set} (f : A → B) : Set where
  constructor mkisequiv
  field
    g : B → A
    h : B → A
    α : (f ○ g) ∼ id
    β : (h ○ f) ∼ id

_≅_ : Set → Set → Set
A ≅ B = Σ[ f ∈ (A → B) ] isequiv f

pathtoequiv : {A B : U} → A ⟷ B → El A ≅ El B
pathtoequiv `id = id , mkisequiv id (λ _ → refl) (λ _ → refl)
pathtoequiv `not = not , mkisequiv not (λ { false → refl ; true → refl }) (λ { false → refl ; true → refl })

equivtopath : {A B : U} → El A ≅ El B → A ⟷ B
equivtopath {`𝟚} {`𝟚} (f , mkisequiv g α β) =
  case f true of (λ { false → `not ; true → `id })
-- what about these cases?
equivtopath {`𝟚} {Paths `id} (f , mkisequiv g α β) = {!!}
equivtopath {`𝟚} {Paths `not} (f , mkisequiv g α β) = {!!}
equivtopath {Paths `id} {`𝟚} (f , mkisequiv g α β) = {!!}
equivtopath {Paths `not} {`𝟚} (f , mkisequiv g α β) = {!!}
equivtopath {Paths `id} {Paths `id} (f , mkisequiv g α β) = {!!}
equivtopath {Paths `id} {Paths `not} (f , mkisequiv g α β) = {!!}
equivtopath {Paths `not} {Paths `id} (f , mkisequiv g α β) = {!!}
equivtopath {Paths `not} {Paths `not} (f , mkisequiv g α β) = {!!}
--}

------------------------------------------------------------------------------
--}
