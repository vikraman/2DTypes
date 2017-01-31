{-# OPTIONS --without-K #-}

module FW where

import Level as L using (_⊔_; zero; suc; lift; Lift)
open import Data.Nat using (ℕ; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Vec
open import Function renaming (_∘_ to _○_)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- For each entity, we first define the syntax in our little language and then
-- the interpretation in conventional HoTT

------------------------------------------------------------------------------
-- The type Bool

data `𝟚 : Set where
  `true : `𝟚
  `false : `𝟚

-- Semantic

𝟚 : Set
𝟚 = Bool

El𝟚 : `𝟚 → 𝟚
El𝟚 `true = true
El𝟚 `false = false

------------------------------------------------------------------------------
-- A universe that contains just Bool

data `U : Set where
  `𝟚U : `U

-- Semantic

ElU : `U → Set
ElU `𝟚U = 𝟚

------------------------------------------------------------------------------
-- A higher universe that contains just `U

data `U1 : Set where
  `UU : `U1

-- Semantic

ElU1 : `U1 → Set
ElU1 `UU = `U

------------------------------------------------------------------------------
-- Functions (only reversible ones)

data _⟶_ : `U → `U → Set where
  `id⟶ : `𝟚U ⟶ `𝟚U
  `not⟶ : `𝟚U ⟶ `𝟚U

comp⟶ : {A B C : `U} → (A ⟶ B) → (B ⟶ C) → (A ⟶ C)
comp⟶ `id⟶ `id⟶ = `id⟶
comp⟶ `id⟶ `not⟶ = `not⟶
comp⟶ `not⟶ `id⟶ = `not⟶
comp⟶ `not⟶ `not⟶ = `id⟶

ap⟶ : {A B : `U} → (A ⟶ B) → `𝟚 → `𝟚
ap⟶ `id⟶ a = a
ap⟶ `not⟶ `true = `false
ap⟶ `not⟶ `false = `true

-- Semantic

El⟶ : {A B : `U} → (A ⟶ B) → ElU A → ElU B
El⟶ `id⟶ = id
El⟶ `not⟶ = not

--

data _⟶u_ : `U1 → `U1 → Set where
  `id⟶u : `UU ⟶u `UU

-- Semantic

El⟶u : `UU ⟶u `UU → `U → `U
El⟶u `id⟶u = id

------------------------------------------------------------------------------
-- Identity types I

data _=𝟚_ : `𝟚 → `𝟚 → Set where
  `idtrue : `true =𝟚 `true
  `idfalse : `false =𝟚 `false

contra𝟚tf : `true =𝟚 `false → ⊥
contra𝟚tf ()

contra𝟚ft : `false =𝟚 `true → ⊥
contra𝟚ft ()

-- Semantic

El=𝟚 : {a b : `𝟚} → a =𝟚 b → El𝟚 a ≡ El𝟚 b
El=𝟚 `idtrue = refl
El=𝟚 `idfalse = refl

------------------------------------------------------------------------------
-- Homotopies

Hom : {A B : `U} → (f g : A ⟶ B) → Set
Hom {`𝟚U} {`𝟚U} f g = ∀ x → ap⟶ f x =𝟚 ap⟶ g x

hom : {A B : `U} → (f : A ⟶ B) → Hom f f
hom `id⟶ `true = `idtrue
hom `id⟶ `false = `idfalse
hom `not⟶ `true = `idfalse
hom `not⟶ `false = `idtrue

-- Semantic

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} →
      (f g : (x : A) → P x) → Set (L._⊔_ ℓ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

refl∼ : {A B : Set} → (f : A → B) → f ∼ f
refl∼ f x = refl

Elap⟶ : {A B : `U} {f g : A ⟶ B} {x : `𝟚} →
         (ap⟶ f x =𝟚 ap⟶ g x) → El⟶ f ∼ El⟶ g
Elap⟶ {f = `id⟶} {`id⟶} h = refl∼ id
Elap⟶ {f = `id⟶} {`not⟶} {`true} h = ⊥-elim (contra𝟚tf h)
Elap⟶ {f = `id⟶} {`not⟶} {`false} h = ⊥-elim (contra𝟚ft h)
Elap⟶ {f = `not⟶} {`id⟶} {`true} h = ⊥-elim (contra𝟚ft h)
Elap⟶ {f = `not⟶} {`id⟶} {`false} h = ⊥-elim (contra𝟚tf h)
Elap⟶ {f = `not⟶} {`not⟶} h = refl∼ not

ElHom : {A B : `U} {f g : A ⟶ B} → Hom f g → El⟶ f ∼ El⟶ g
ElHom {`𝟚U} {`𝟚U} {f} {g} h false = Elap⟶ {f = f} {g = g} (h `false) false
ElHom {`𝟚U} {`𝟚U} {f} {g} h true = Elap⟶ {f = f} {g = g} (h `true) true

------------------------------------------------------------------------------
-- Equivalences

EquivU : `U → `U → Set
EquivU `𝟚U `𝟚U = Σ[ f ∈ `𝟚U ⟶ `𝟚U ]
                 Σ[ g ∈ `𝟚U ⟶ `𝟚U ]
                 Σ[ h ∈ `𝟚U ⟶ `𝟚U ]
                 Hom (comp⟶ g f) `id⟶ × Hom (comp⟶ f h) `id⟶

`idequiv : EquivU `𝟚U `𝟚U
`idequiv = `id⟶ , `id⟶ , `id⟶ , hom `id⟶ , hom `id⟶

`notequiv : EquivU `𝟚U `𝟚U
`notequiv = `not⟶ , `not⟶ , `not⟶ , hom `id⟶ , hom `id⟶

-- Semantic

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) :
  Set (L._⊔_ ℓ ℓ') where
  constructor mkqinv
  field
    g : B → A
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) :
  Set (L._⊔_ ℓ ℓ') where
  constructor mkisequiv
  field
    g : B → A
    α : (f ○ g) ∼ id
    h : B → A
    β : (h ○ f) ∼ id

equiv₁ : ∀ {ℓ ℓ'} →
         {A : Set ℓ} {B : Set ℓ'} {f : A → B} → qinv f → isequiv f
equiv₁ (mkqinv qg qα qβ) = mkisequiv qg qα qg qβ

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (L._⊔_ ℓ ℓ')
A ≃ B = Σ (A → B) isequiv

idequiv : Bool ≃ Bool
idequiv = id , equiv₁ (mkqinv id
                       (λ { false → refl; true → refl})
                       (λ { false → refl; true → refl}))

notequiv : Bool ≃ Bool
notequiv = not , equiv₁ (mkqinv not
                       (λ { false → refl; true → refl})
                       (λ { false → refl; true → refl}))

------------------------------------------------------------------------------
-- Identity types II

data _⟷_ : `U → `U → Set where
  `id⟷ : {A : `U} → A ⟷ A
  `not⟷ : `𝟚U ⟷ `𝟚U

-- Semantic

postulate
  univalence : {A B : Set} → (A ≡ B) ≃ (A ≃ B)

notpath : Bool ≡ Bool
notpath = isequiv.g (proj₂ univalence) notequiv

El⟷ : {A B : `U} → (A ⟷ B) → ElU A ≡ ElU B
El⟷ `id⟷ = refl
El⟷ `not⟷ = notpath

--

-----------
-- JC how is ⟶ different from ⟷ ?  They seem the same here, in that
⟶Proves≡ : {A B : `U} → (A ⟶ B) → ElU A ≡ ElU B
⟶Proves≡ `id⟶ = refl
⟶Proves≡ `not⟶ = notpath
-----------

--
data _⇔_ : {A B : `U} → (A ⟷ B) → (A ⟷ B) → Set where
  id⇔ : {A B : `U} {c : A ⟷ B} → c ⇔ c

-- Semantic

El⇔ : {A B : `U} {c₁ c₂ : A ⟷ B} → (c₁ ⇔ c₂) → El⟷ c₁ ≡ El⟷ c₂
El⇔ id⇔ = refl

------------------------------------------------------------------------------
-- Functions II

data `UF : (A B : `U) → Set where
  ID : {A : `U} → `UF A A
  E : {A B : `U} → EquivU A B → `UF A B
  P : {A B : `U} → (A ⟷ B) → `UF A B

_⇒_ : {A B : `U} → `UF A B → `UF A B → Set
_⇒_ {`𝟚U} {`𝟚U} (E (f₁ , g₁ , h₁ , α₁ , β₁)) (E (f₂ , g₂ , h₂ , α₂ , β₂)) = {!!}
_⇒_ {`𝟚U} {`𝟚U} (E (f , g , h , α , β)) (P p) = {!!}
_⇒_ {`𝟚U} {`𝟚U} (P p) (E (f , g , h , α , β)) = {!!}
_⇒_ {A} {.A} (P `id⟷) (P `id⟷) = _⇔_ {A} `id⟷ `id⟷
P `id⟷ ⇒ P `not⟷ = ⊥
P `not⟷ ⇒ P `id⟷ = ⊥
_⇒_ {`𝟚U} {`𝟚U} (P `not⟷) (P `not⟷) = _⇔_ `not⟷ `not⟷
_⇒_ _ _ = {!!}

comp⇒ : {A B : `U} {F G H : `UF A B} → F ⇒ G → G ⇒ H → F ⇒ H
comp⇒ = {!!}

------------------------------------------------------------------------------
-- Homotopies II

HomF : {A B : `U} → (F G : `UF A B) → Set
HomF F G = {!!} -- ∀ x → ap⟶ f x =𝟚 ap⟶ g x

------------------------------------------------------------------------------
-- Equivalence II

EquivUF : {A B : `U} → `UF A B → `UF A B → Set
EquivUF {A} {B} F G =
  Σ[ f ∈ F ⇒ G ]
  Σ[ g ∈ G ⇒ F ]
  Σ[ h ∈ G ⇒ F ]
  ?

------------------------------------------------------------------------------
-- Dependent pairs, dependent functions, and J

-- We could in principle add syntax for all the dependent pairs and functions we
-- want but it gets quite messy. So we will use Agda to express these entities
-- but we will create a universe `ℙ that captures all the properties that we
-- want to express using these dependent pairs and functions.

data `ℙ : Set where
  _`⟷_ : (A B : `U) → `ℙ
  `ΣF : (A B : `U) → `ℙ

Elℙ : `ℙ → Set
Elℙ (A `⟷ B) = A ⟷ B
Elℙ (`ΣF A B) = (A ⟷ `𝟚U) → (B ⟷ `𝟚U)

J : (C : {A B : `U} → (A ⟷ B) → `ℙ) →
    (cid : {A : `U} → Elℙ (C {A} `id⟷)) → (cnot : Elℙ (C `not⟷)) →
    ({A B : `U} (p : A ⟷ B) → Elℙ (C p))
J C cid cnot `id⟷ = cid
J C cid cnot `not⟷ = cnot

--

! : {A B : `U} → A ⟷ B → B ⟷ A
! = J (λ {A} {B} _ → B `⟷ A) `id⟷ `not⟷

ap : (f : `UU ⟶u `UU) → (`𝟚U ⟷ `𝟚U) → (El⟶u f `𝟚U ⟷ El⟶u f `𝟚U)
ap `id⟶u = J (λ _ → `𝟚U `⟷ `𝟚U) `id⟷ `not⟷

transport : {A B : `U} → (A ⟷ B) → (A ⟷ `𝟚U) → (B ⟷ `𝟚U)
transport = J (λ {A} {B} _ → `ΣF A B) (λ {A} → id) g
  where g : (`𝟚U ⟷ `𝟚U) → (`𝟚U ⟷ `𝟚U)
        g `id⟷ = `not⟷
        g `not⟷ = `id⟷

X1 X2 X3 X4 : `𝟚U ⟷ `𝟚U
X1 = transport `id⟷ `id⟷ -- ==> `id⟷
X2 = transport `id⟷ `not⟷ -- ==> `not⟷
X3 = transport `not⟷ `id⟷ -- ==> `not⟷
X4 = transport `not⟷ `not⟷ -- ==> `id⟷

------------------------------------------------------------------------------
-- Lemmas

`univalence : {A B : `U} {c : A ⟷ B} {eq : EquivU A B} → EquivUF (P c) (E eq)
`univalence {`𝟚U} {`𝟚U} = {!!}

------------------------------------------------------------------------------
-- HITs

data `Frac : Set where
  -- generalize to pointed types [#c,cᵏ] ... add ∀ ∃
  `# : {A B : `U} → A ⟷ B → `Frac
  `1/# : {A B : `U} → A ⟷ B → `Frac
  _⊠_ : `Frac → `Frac → `Frac

ElFrac : `Frac → Set
ElFrac (`# c) = {!!} -- c^k
ElFrac (`1/# c) = {!!} -- 1/c^k
ElFrac (T₁ ⊠ T₂) = ElFrac T₁ × ElFrac T₂

data _⟪=⟫_ : `Frac → `Frac → Set where
  unitel : {A : `U} {T : `Frac} → (`# (`id⟷ {A}) ⊠ T) ⟪=⟫ T
  unitil : {A : `U} {T : `Frac} → T ⟪=⟫ (`# (`id⟷ {A}) ⊠ T)
  uniter : {A : `U} {T : `Frac} → (T ⊠ (`# (`id⟷ {A}))) ⟪=⟫ T
  unitir : {A : `U} {T : `Frac} → T ⟪=⟫ (T ⊠ (`# (`id⟷ {A})))
  η- : {A B C : `U} {c : B ⟷ C} → (`# (`id⟷ {A})) ⟪=⟫ (`1/# c ⊠ `# c)
  -- ε-
  -- η+
  -- ε+
  -- id/
  -- ◍
  -- `#
  -- ⊗

------------------------------------------------------------------------------






































{--
infixr 8  _∘_   -- path composition
infix  4  _≡_   -- propositional equality
infix  4  _∼_   -- homotopy between two functions (the same as ≡ by univalence)
infix  4  _≃_   -- type of equivalences
infix  2  _∎      -- equational reasoning
infixr 2  _≡⟨_⟩_  -- equational reasoning

------------------------------------------------------------------------------
-- Identity types

-- Our own version of refl that makes 'a' explicit

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)

-- Induction principle for identity types

pathInd : ∀ {u ℓ} → {A : Set u} →
          (C : {x y : A} → x ≡ y → Set ℓ) →
          (c : (x : A) → C (refl x)) →
          ({x y : A} (p : x ≡ y) → C p)
pathInd C c (refl x) = c x

------------------------------------------------------------------------------
-- Types are higher groupoids. We have paths between the elements
-- (refl, sym, trans) then we have path between paths, e.g., paths
-- between p and (trans p refl) and paths between (sym (sym p)) and p
-- etc.

-- Lemma 2.1.1

! : ∀ {u} → {A : Set u} {x y : A} → (x ≡ y) → (y ≡ x)
! = pathInd (λ {x} {y} _ → y ≡ x) refl

-- Lemma 2.1.2

_∘_ : ∀ {u} → {A : Set u} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_∘_ {u} {A} {x} {y} {z} p q =
  pathInd {u}
    (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (x ≡ z)))
    (λ x z q → pathInd (λ {x} {z} _ → x ≡ z) refl {x} {z} q)
    {x} {y} p z q

-- Lemma 2.1.4

-- p = p . refl

unitTransR : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ p ∘ refl y)
unitTransR {A} {x} {y} p =
  pathInd
    (λ {x} {y} p → p ≡ p ∘ (refl y))
    (λ x → refl (refl x))
    {x} {y} p

-- p = refl . p

unitTransL : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ refl x ∘ p)
unitTransL {A} {x} {y} p =
  pathInd
    (λ {x} {y} p → p ≡ (refl x) ∘ p)
    (λ x → refl (refl x))
    {x} {y} p

-- ! p . p = refl

invTransL : {A : Set} {x y : A} → (p : x ≡ y) → (! p ∘ p ≡ refl y)
invTransL {A} {x} {y} p =
  pathInd
    (λ {x} {y} p → ! p ∘ p ≡ refl y)
    (λ x → refl (refl x))
    {x} {y} p

-- p . ! p = refl

invTransR : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → (p ∘ ! p ≡ refl x)
invTransR {ℓ} {A} {x} {y} p =
  pathInd
    (λ {x} {y} p → p ∘ ! p ≡ refl x)
    (λ x → refl (refl x))
    {x} {y} p

-- ! (! p) = p

invId : {A : Set} {x y : A} → (p : x ≡ y) → (! (! p) ≡ p)
invId {A} {x} {y} p =
  pathInd
    (λ {x} {y} p → ! (! p) ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

-- p . (q . r) = (p . q) . r

assocP : {A : Set} {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) →
         (p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
assocP {A} {x} {y} {z} {w} p q r =
  pathInd
    (λ {x} {y} p → (z : A) → (w : A) → (q : y ≡ z) → (r : z ≡ w) →
      p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
    (λ x z w q r →
      pathInd
        (λ {x} {z} q → (w : A) → (r : z ≡ w) →
          (refl x) ∘ (q ∘ r) ≡ ((refl x) ∘ q) ∘ r)
        (λ x w r →
          pathInd
            (λ {x} {w} r →
              (refl x) ∘ ((refl x) ∘ r) ≡
              ((refl x) ∘ (refl x)) ∘ r)
            (λ x → (refl (refl x)))
            {x} {w} r)
        {x} {z} q w r)
    {x} {y} p z w q r

-- ! (p ∘ q) ≡ ! q ∘ ! p

invComp : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) →
          ! (p ∘ q) ≡ ! q ∘ ! p
invComp {A} {x} {y} {z} p q =
  pathInd
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → ! (p ∘ q) ≡ ! q ∘ ! p)
    (λ x z q →
      pathInd
        (λ {x} {z} q → ! (refl x ∘ q) ≡ ! q ∘ ! (refl x))
        (λ x → refl (refl x))
        {x} {z} q)
    {x} {y} p z q

-- Introduce equational reasoning syntax to simplify proofs

_≡⟨_⟩_ : ∀ {u} → {A : Set u} (x : A) {y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_ ≡⟨ p ⟩ q = p ∘ q

bydef : ∀ {u} → {A : Set u} {x : A} → (x ≡ x)
bydef {u} {A} {x} = refl x

_∎ : ∀ {u} → {A : Set u} (x : A) → x ≡ x
_∎ x = refl x

------------------------------------------------------------------------------
-- Functions are functors

-- Lemma 2.2.1
-- computation rule: ap f (refl x) = refl (f x)

ap : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A} →
     (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {ℓ} {ℓ'} {A} {B} {x} {y} f p =
  pathInd -- on p
    (λ {x} {y} p → f x ≡ f y)
    (λ x → refl (f x))
    {x} {y} p

-- Lemma 2.2.2

apfTrans : ∀ {u} → {A B : Set u} {x y z : A} →
  (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q)
apfTrans {u} {A} {B} {x} {y} {z} f p q =
  pathInd {u}
    (λ {x} {y} p → (z : A) → (q : y ≡ z) →
      ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q))
    (λ x z q →
      pathInd {u}
        (λ {x} {z} q →
          ap f (refl x ∘ q) ≡ (ap f (refl x)) ∘ (ap f q))
        (λ x → refl (refl (f x)))
        {x} {z} q)
    {x} {y} p z q

apfInv : ∀ {u} → {A B : Set u} {x y : A} → (f : A → B) → (p : x ≡ y) →
         ap f (! p) ≡ ! (ap f p)
apfInv {u} {A} {B} {x} {y} f p =
  pathInd {u}
    (λ {x} {y} p → ap f (! p) ≡ ! (ap f p))
    (λ x → refl (ap f (refl x)))
    {x} {y} p

apfComp : {A B C : Set} {x y : A} → (f : A → B) → (g : B → C) → (p : x ≡ y) →
          ap g (ap f p) ≡ ap (g ○ f) p
apfComp {A} {B} {C} {x} {y} f g p =
  pathInd
    (λ {x} {y} p → ap g (ap f p) ≡ ap (g ○ f) p)
    (λ x → refl (ap g (ap f (refl x))))
    {x} {y} p

apfId : {A : Set} {x y : A} → (p : x ≡ y) → ap id p ≡ p
apfId {A} {x} {y} p =
  pathInd
    (λ {x} {y} p → ap id p ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

-- Transport; Lifting

-- Lemma 2.3.1

transport : ∀ {ℓ ℓ'} → {A : Set ℓ} {x y : A} →
  (P : A → Set ℓ') → (p : x ≡ y) → P x → P y
transport {ℓ} {ℓ'} {A} {x} {y} P p =
  pathInd -- on p
    (λ {x} {y} p → (P x → P y))
    (λ _ → id)
    {x} {y} p

stransport : ∀ {ℓ} → {A : Set ℓ} {x y : A} → (p : x ≡ y) → A → A
stransport {ℓ} {A} {x} {y} p = transport {ℓ} {ℓ} {A} {x} {y} (λ _ → A) p

-- Lemma 2.3.2

liftP : {A : Set} {x y : A} {P : A → Set} → (u : P x) → (p : x ≡ y) →
        (x , u) ≡ (y , transport P p u)
liftP {A} {x} {y} {P} u p =
  pathInd
    (λ {x} {y} p → ((u : P x) → (x , u) ≡ (y , transport P p u)))
    (λ x u → refl (x , u))
    {x} {y} p u

-- Lemma 2.3.4 (dependent version of Lemma 2.2.1)

apd : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : A → Set ℓ'} {x y : A} → (f : (a : A) → B a) →
  (p : x ≡ y) → (transport B p (f x) ≡ f y)
apd {ℓ} {ℓ'} {A} {B} {x} {y} f p =
  pathInd
    (λ {x} {y} p → transport B p (f x) ≡ f y)
    (λ x → refl (f x))
    {x} {y} p

-- Lemma 2.3.5

transportconst : {A : Set} {x y : A} → (B : Set) → (p : x ≡ y) → (b : B) →
                 (transport (λ _ → B) p b ≡ b)
transportconst {A} {x} {y} B p b =
  pathInd
    (λ {x} {y} p → transport (λ _ → B) p b ≡ b)
    (λ _ → refl b)
    {x} {y} p

-- Eqs. 2.3.6 and 2.3.7

transportconst-ap : {A : Set} {x y : A} → (B : Set) → (p : x ≡ y) →
  (f : A → B) → (f x ≡ f y) → (transport (λ _ → B) p (f x) ≡ f y)
transportconst-ap {A} {x} {y} B p f α =
  transportconst B p (f x) ∘ α

ap-transportconst : {A : Set} {x y : A} → (B : Set) → (p : x ≡ y) →
  (f : A → B) → (transport (λ _ → B) p (f x) ≡ f y) → (f x ≡ f y)
ap-transportconst {A} {x} {y} B p f α =
  (! (transportconst B p (f x))) ∘ α

-- Lemma 2.3.8

apd-transportconst : {A : Set} {x y : A} → (B : Set) → (p : x ≡ y) →
  (f : A → B) → (apd f p ≡ transportconst B p (f x) ∘ ap f p)
apd-transportconst {A} {x} {y} B p f =
  pathInd -- on p
    (λ {x} {y} p → apd f p ≡ transportconst B p (f x) ∘ ap f p)
    (λ x → refl (refl (f x)))
    {x} {y} p

-- Lemma 2.3.9

transport-comp : {A : Set} {x y z : A} → (P : A → Set) →
  (p : x ≡ y) → (q : y ≡ z) →
  (u : P x) → transport P q (transport P p u) ≡ transport P (p ∘ q) u
transport-comp {A} {x} {y} {z} P p q u =
  pathInd -- on p
    (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (u : P x) →
      transport P q (transport P p u) ≡ transport P (p ∘ q) u))
    (λ x z q u →
      pathInd -- on q
        (λ {x} {z} q → ((u : P x) →
          transport P q (transport P (refl x) u) ≡
          transport P (refl x ∘ q) u))
        (λ x u → refl u)
        {x} {z} q u)
    {x} {y} p z q u

-- Lemma 2.3.10

transport-f : ∀ {ℓ ℓ' ℓ''} → {A : Set ℓ} {B : Set ℓ'} {x y : A} →
  (f : A → B) → (P : B → Set ℓ'') →
  (p : x ≡ y) → (u : P (f x)) →
  transport (P ○ f) p u ≡ transport P (ap f p) u
transport-f {ℓ} {ℓ'} {ℓ''} {A} {B} {x} {y} f P p u =
  pathInd -- on p
    (λ {x} {y} p → (u : P (f x)) →
      transport (P ○ f) p u ≡ transport P (ap f p) u)
    (λ x u → refl u)
    {x} {y} p u

-- Lemma 2.3.11

transport-fam : ∀ {ℓ} → {A : Set ℓ} {x y : A} → (P Q : A → Set ℓ) →
  (f : (a : A) → P a → Q a) → (p : x ≡ y) → (u : P x) →
  transport Q p (f x u) ≡ f y (transport P p u)
transport-fam {ℓ} {A} {x} {y} P Q f p u =
  pathInd {ℓ} -- on p
    (λ {x} {y} p → (u : P x) →
      transport Q p (f x u) ≡ f y (transport P p u))
    (λ x u → refl (f x u))
    {x} {y} p u

-------------------------------------------------------------------------------
-- Homotopies and equivalences

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} →
      (f g : (x : A) → P x) → Set (L._⊔_ ℓ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

-- Lemma 2.4.2

refl∼ : {A B : Set} {f : A → B} → (f ∼ f)
refl∼ {A} {B} {f} x = refl (f x)

sym∼ : {A B : Set} {f g : A → B} → (f ∼ g) → (g ∼ f)
sym∼ H x = ! (H x)

trans∼ : {A B : Set} {f g h : A → B} → (f ∼ g) → (g ∼ h) → (f ∼ h)
trans∼ H G x = H x ∘ G x

-- Quasi-inverses

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) :
  Set (L._⊔_ ℓ ℓ') where
  constructor mkqinv
  field
    g : B → A
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

-- Example 2.4.7

idqinv : ∀ {ℓ} → {A : Set ℓ} → qinv {ℓ} {ℓ} {A} {A} id
idqinv = record {
           g = id ;
           α = λ b → refl b ;
           β = λ a → refl a
         }

-- Equivalences

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) :
  Set (L._⊔_ ℓ ℓ') where
  constructor mkisequiv
  field
    g : B → A
    α : (f ○ g) ∼ id
    h : B → A
    β : (h ○ f) ∼ id

equiv₁ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {f : A → B} → qinv f → isequiv f
equiv₁ (mkqinv qg qα qβ) = mkisequiv qg qα qg qβ

equiv₂ : {A B : Set} {f : A → B} → isequiv f → qinv f
equiv₂ {A} {B} {f} (mkisequiv ig iα ih iβ) =
  record {
    g = ig ;
    α = iα ;
    β = λ x → (! (iβ (ig (f x)))) ∘ (ap ih (iα (f x))) ∘ (iβ x)
    }

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (L._⊔_ ℓ ℓ')
A ≃ B = Σ (A → B) isequiv

-- Lemma 2.4.12

idequiv : ∀ {ℓ} {A : Set ℓ} → A ≃ A
idequiv = (id , equiv₁ idqinv)

symequiv : {A B : Set} → A ≃ B → B ≃ A
symequiv (f , feq) with equiv₂ feq
... | mkqinv g α β = (g , equiv₁ (mkqinv f β α))

------------------------------------------------------------------------------
-- Now we try to understand the structure of the paths. For how are
-- paths defined on pairs related to the paths on the individual
-- elements...

-- Sec. 2.6: cartesian products
-- implicit use of recP below to that arguments of product types are
-- pairs; "eliminators" for paths on pairs

ap_pr₁ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
        (x ≡ y) → (proj₁ x ≡ proj₁ y)
ap_pr₁ = ap proj₁

ap_pr₂ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
         (x ≡ y) → (proj₂ x ≡ proj₂ y)
ap_pr₂ = ap proj₂

-- Eq. 2.6.1

fpair : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
        (x ≡ y) → ((proj₁ x ≡ proj₁ y) × (proj₂ x ≡ proj₂ y))
fpair p = (ap_pr₁ p , ap_pr₂ p)

-- "constructor" for paths on pairs

pair⁼ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
        (proj₁ x ≡ proj₁ y) × (proj₂ x ≡ proj₂ y) → (x ≡ y)
pair⁼ {ℓ} {ℓ'} {A} {B} {(a , b)} {(a' , b')} (p , q) =
  pathInd -- on p
    (λ {a} {a'} p → ((b : B) → (b' : B) → (q : b ≡ b') →
      ((a , b) ≡ (a' , b'))))
    (λ a b b' q →
      pathInd -- on q
        (λ {b} {b'} q → (a , b) ≡ (a , b'))
        (λ b → refl (a , b))
        {b} {b'} q)
    {a} {a'} p b b' q

-- propositional uniqueness for pairs as a consequence

upair : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {z : A × B} → z ≡ (proj₁ z , proj₂ z)
upair {ℓ} {ℓ'} {A} {B} {z} =
  pair⁼ {ℓ} {ℓ'} {A} {B} {z} {(proj₁ z , proj₂ z)}
    (refl (proj₁ z) , refl (proj₂ z))

-- "computation rules" for paths on pairs

βpair : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
        (r : x ≡ y) → (pair⁼ (fpair r) ≡ r)
βpair {ℓ} {ℓ'} {A} {B} {x} {y} r =
  pathInd -- on r
    (λ {x} {y} r → pair⁼ (fpair r) ≡ r)
    (λ x → refl (refl (proj₁ x , proj₂ x)))
    {x} {y} r

-- propositional uniqueness principle for pairs of paths

upairp : ∀ {u} {A B : Set u} {x y : A × B} {r : x ≡ y} →
         r ≡ pair⁼ (ap_pr₁ r , ap_pr₂ r)
upairp {u} {A} {B} {x} {y} {r} = ! (βpair {u} {u} {A} {B} {x} {y} r)

-- Theorem 2.6.4

_×d_ : {Z : Set} → (A B : Z → Set) → (z : Z) → Set
_×d_ {Z} A B z = A z × B z

-- Theorem 2.6.5

pairf : {A B A' B' : Set} {g : A → A'} {h : B → B'} →
        A × B → A' × B'
pairf {A} {B} {A'} {B'} {g} {h} x = (g (proj₁ x) , h (proj₂ x))

------------------------------------------------------------------------------
-- Sec. 2.7: Σ-types

sigma⁼ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {w w' : Σ A P} →
         (Σ (proj₁ w ≡ proj₁ w') (λ p → transport P p (proj₂ w) ≡ proj₂ w'))
         → (w ≡ w')
sigma⁼ {ℓ} {ℓ'} {A} {P} {(w₁ , w₂)} {(w₁' , w₂')} (p , q) =
  pathInd -- on p
    (λ {w₁} {w₁'} p → (w₂ : P w₁) → (w₂' : P w₁') →
                     (q : transport P p w₂ ≡ w₂') → ((w₁ , w₂) ≡ (w₁' , w₂')))
    (λ w₁ w₂ w₂' q →
      pathInd -- on q
        (λ {w₂} {w₂'} q → (w₁ , w₂) ≡ (w₁ , w₂'))
        (λ w₂ → refl (w₁ , w₂))
        {w₂} {w₂'} q)
    {w₁} {w₁'} p w₂ w₂' q

-- Thm 2.7.4 transport

transportΣ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {P : A → Set ℓ'} {Q : Σ A P → Set ℓ''}
  {x y : A} → (p : x ≡ y) → (uz : Σ (P x) (λ u → Q (x , u))) →
  transport (λ x → Σ (P x) (λ u → Q (x , u))) p uz ≡
    (transport P p (proj₁ uz) ,
     transport Q (sigma⁼ (p , refl (transport P p (proj₁ uz)))) (proj₂ uz))
transportΣ {ℓ} {ℓ'} {ℓ''} {A} {P} {Q} {x} {y} p (u , z) =
  pathInd -- on p
    (λ {x} {y} p → (uz : Σ (P x) (λ u → Q (x , u))) →
      transport (λ x → Σ (P x) (λ u → Q (x , u))) p uz ≡
      (transport P p (proj₁ uz) ,
        transport Q (sigma⁼ (p , refl (transport P p (proj₁ uz)))) (proj₂ uz)))
    (λ x uz → refl uz)
    {x} {y} p (u , z)

------------------------------------------------------------------------------
-- Sec. 2.8: Unit type

unitPath : {x y : ⊤} → (x ≡ y) ≃ ⊤
unitPath {x} {y} =
  ((λ _ → tt) , equiv₁ (record {
    g = λ _ → refl tt ;
    α = λ _ → refl tt ;
    β = λ p → pathInd
                (λ {_} {_} p → refl tt ≡ p)
                (λ _ → refl (refl tt))
                {x} {y} p
  }))

------------------------------------------------------------------------------
-- Sec. 2.9: Pi types; function extensionality

happly : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (a : A) → B a} →
         (f ≡ g) → (f ∼ g)
happly {ℓ} {ℓ'} {A} {B} {f} {g} p =
  pathInd
    (λ {f} {g} p → f ∼ g)
    (λ f x → refl (f x))
    {f} {g} p

postulate
  funextP : {A : Set} {B : A → Set} {f g : (a : A) → B a} →
            isequiv {A = f ≡ g} {B = f ∼ g} happly

funext : {A : Set} {B : A → Set} {f g : (a : A) → B a} →
         (f ∼ g) → (f ≡ g)
funext = isequiv.g funextP

------------------------------------------------------------------------------
-- Sec. 2.10: Universes; univalence

idtoeqv : {A B : Set} → (A ≡ B) → (A ≃ B)
idtoeqv {A} {B} p =
  pathInd
    (λ {A} {B} p → A ≃ B)
    (λ A → idequiv)
    {A} {B} p

postulate
  univalence : {A B : Set} → (A ≡ B) ≃ (A ≃ B)

------------------------------------------------------------------------------
-- Bool

noteq : Bool ≃ Bool
noteq = not , equiv₁ (mkqinv not
                       (λ { false → refl false; true → refl true})
                       (λ { false → refl false; true → refl true}))

notpath : Bool ≡ Bool
notpath = isequiv.g (proj₂ univalence) noteq

-- Now go back and look at what happens to notpath

!notpath : Bool ≡ Bool
!notpath = ! notpath

notnotpath : Bool ≡ Bool
notnotpath = notpath ∘ notpath

!notnotpath : Bool ≡ Bool
!notnotpath = !notpath ∘ notpath

⊤⊤path : (⊤ ⊎ ⊤) ≡ (⊤ ⊎ ⊤)
⊤⊤path = ap (λ _ → ⊤ ⊎ ⊤) notpath

⊤⊤fun : (⊤ ⊎ ⊤) → (⊤ ⊎ ⊤)
⊤⊤fun = transport (λ _ → ⊤ ⊎ ⊤) notpath

-- ⊤⊤fun (inj₁ tt) does not compute obviously

notdetour : Bool → Bool
notdetour = transport id notpath

-- notdetour false does not compute obviously

------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------

------------------------------------------------------------------------------

𝟚 : Set
𝟚 = Bool

data `U : Set
data 𝟚⟷𝟚 : Set

data `U where
  `𝟚 : `U
  1-Paths : `U -- 𝟚 ⟷ 𝟚
  2-Paths : (c₁ c₂ : 𝟚⟷𝟚) → `U

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

J𝟚 : (cid : 𝟚⟷𝟚) → (cnot : 𝟚⟷𝟚) →
     (p : 𝟚⟷𝟚) → 𝟚⟷𝟚
J𝟚 cid cnot `id = cid
J𝟚 cid cnot `not = cnot

-- Lemma 2.1.1

_⁻¹ : 𝟚⟷𝟚 → 𝟚⟷𝟚
_⁻¹ = 1pathInd (λ _ → 𝟚⟷𝟚) `id `not

-- ap
-- Only functions in our universe are the functions coming from equivalences/paths

path2fun : (𝟚⟷𝟚) → 𝟚 → 𝟚
path2fun `id = id
path2fun `not = not

AP : (f : 𝟚⟷𝟚) → (p : 𝟚⟷𝟚) → 𝟚⟷𝟚
AP `id p = p
AP `not `id = `not
AP `not `not = `id

-- Now we should be able to write AP using some version of J

JJ : 𝟚⟷𝟚 → 𝟚⟷𝟚 → 𝟚⟷𝟚 → 𝟚⟷𝟚 → 𝟚⟷𝟚
JJ `id cid cnot p = p
JJ `not cid cnot `id = cnot
JJ `not cid cnot `not = cid

APJ : (f : 𝟚⟷𝟚) → (p : 𝟚⟷𝟚) → 𝟚⟷𝟚
APJ f = JJ f `id `not

-- Will use pattern-matching instead of the explicit induction principle in the
-- following

{--
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

{--
univalence : (𝟚⟷𝟚) ≅ (𝟚 ≅ 𝟚)
univalence = pathtoequiv , mkisequiv equivtopath α β
  where β :  (equivtopath ○ pathtoequiv) ∼ id
        β `id = refl
        β `not = refl

        α : (pathtoequiv ○ equivtopath) ∼ id
        α (f , mkisequiv g h₁ h₂) with equivtopath (f , mkisequiv g h₁ h₂)
        ... | `id = cong₂D! _,_ (funext {!!}) {!!}
        ... | `not = cong₂D! _,_ (funext {!!}) {!!}

        -- Courtesy of Wolfram Kahl, a dependent cong₂
        cong₂D! : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
                  (f : (x : A) → B x → C)
                  → {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
                  → (x₂≡x₁ : x₂ ≡ x₁) → subst B x₂≡x₁ y₂ ≡ y₁ → f x₁ y₁ ≡ f x₂ y₂
        cong₂D! f refl refl = refl
--}

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
--}
