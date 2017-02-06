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
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary
open import Function
open import Relation.Binary.PropositionalEquality

infix  30 _⟷_
infixr 50 _◎_

------------------------------------------------------------------------------
-- The universe of types

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

-- size of `𝟚 is 2 and here are the two values
false true : El `𝟚
false = inj₁ tt
true = inj₂ tt

-- size of EQ a b is tentatively 1 or 0 depending on whether a ≡ b or not

`A : U
`A = SIGMA `𝟚 (λ b → EQ {`𝟚} b false)

-- size of `A is calculated as follows:
--   for every value b in `𝟚, we calculate the size of EQ {`𝟚} b false
--   if b is false, the type false ≡ false has one element (refl)
--   if b is true, the type true ≡ false is empty
--   we sum the sizes; the total size is 1 and here is the value
a : El `A
a = false , refl

`B : U
`B = PI `𝟚 (λ a → SIGMA `𝟚 (λ b → EQ {`𝟚} a b))

-- size of `B is calculated as follows:
--   first we calculate the size of each fiber that takes a particular a in `𝟚
--   a function is defined is all its fibers are defined, if any fiber is empty
--     the function cannot be defined
--   so we multiply the number of fibers to get the total size
--   in our case the fiber false can produce one value in SIGMA `𝟚 (λ b → EQ {`𝟚} false b)
--   the fiber true can produce one value in SIGMA `𝟚 (λ b → EQ {`𝟚} true b)
--   hence there is exactly one function in `B and here it is
f : El `B
f (inj₁ tt) = false , refl
f (inj₂ tt) = true , refl

------------------------------------------------------------------------------
-- Some infrastructure (including some HoTT machinery)

postulate
  funext : {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

inj₁lem : {A B : Set} {x y : A} → _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y) → x ≡ y
inj₁lem refl = refl

inj₂lem : {A B : Set} {x y : B} → _≡_ {A = A ⊎ B} (inj₂ x) (inj₂ y) → x ≡ y
inj₂lem refl = refl

inj₁lem' : {A B : Set} {x : A} {y : B} → _≡_ {A = A ⊎ B} (inj₁ x) (inj₂ y) → ⊥
inj₁lem' ()

inj₂lem' : {A B : Set} {x : B} {y : A} → _≡_ {A = A ⊎ B} (inj₂ x) (inj₁ y) → ⊥
inj₂lem' ()

proj₁lem : {A B : Set} {x y : A} {z w : B} → (x , z) ≡ (y , w) → x ≡ y
proj₁lem refl = refl

proj₂lem : {A B : Set} {x y : A} {z w : B} → (x , z) ≡ (y , w) → z ≡ w
proj₂lem refl = refl

--

transport : ∀ {ℓ ℓ'} → {A : Set ℓ} {x y : A} →
            (P : A → Set ℓ') → (p : x ≡ y) → P x → P y
transport P refl = id

fsigma : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {w w' : Σ A P} →
         (w ≡ w') → (Σ (proj₁ w ≡ proj₁ w')
                    (λ p → transport P p (proj₂ w) ≡ proj₂ w'))
fsigma refl = refl , refl

proj₂dlem : {A : Set} {B : A → Set} {x : A} {z w : B x} →
            (q : _≡_ {A = Σ A B} (x , z) (x , w)) →
            -- z ≡ w (bogus: see below)
            Σ[ p ∈ (x ≡ x) ] transport B p z ≡ w
proj₂dlem = fsigma
{--
Remark 2.7.1. Note that if we have x : A and u,v : P(x) such that (x,u) = (x,v),
it does not follow that u = v. All we can conclude is that there exists p : x =
x such that p∗(u) = v. This is a well-known source of confusion for newcomers to
type theory, but it makes sense from a topological viewpoint: the existence of a
path (x, u) = (x, v) in the total space of a fibration between two points that
happen to lie in the same fiber does not imply the existence of a path u = v
lying entirely within that fiber.
--}

_≟_ : {A : U} → Decidable {A = El A} _≡_
_≟_ {ZERO} ()
_≟_ {ONE} tt tt = yes refl
_≟_ {PLUS A B} (inj₁ x) (inj₁ y) with _≟_ {A} x y
_≟_ {PLUS A B} (inj₁ x) (inj₁ .x) | yes refl = yes refl
... | no ¬p = no (¬p ∘ inj₁lem)
_≟_ {PLUS A B} (inj₁ x) (inj₂ y) = no inj₁lem'
_≟_ {PLUS A B} (inj₂ x) (inj₁ y) = no inj₂lem'
_≟_ {PLUS A B} (inj₂ x) (inj₂ y) with _≟_ {B} x y
_≟_ {PLUS A B} (inj₂ x) (inj₂ .x) | yes refl = yes refl
... | no ¬p = no (¬p ∘ inj₂lem)
_≟_ {TIMES A B} (x , y) (z , w) with _≟_ {A} x z | _≟_ {B} y w
_≟_ {TIMES A B} (x , y) (.x , .y) | yes refl | yes refl = yes refl
_≟_ {TIMES A B} (x , y) (z , w) | no ¬p | _ = no (¬p ∘ proj₁lem)
_≟_ {TIMES A B} (x , y) (z , w) | _ | no ¬p = no (¬p ∘ proj₂lem)
_≟_ {SIGMA A P} (x , y) (z , w) with _≟_ {A} x z
_≟_ {SIGMA A P} (x , y) (z , w) | no ¬p = no (¬p ∘ cong proj₁)
_≟_ {SIGMA A P} (x , y) (.x , w) | yes refl with _≟_ {P x} y w
_≟_ {SIGMA A P} (x , y) (.x , .y) | yes refl | yes refl = yes refl
_≟_ {SIGMA A P} (x , y) (.x , w) | yes refl | no ¬p = no {!!}
_≟_ {PI A P} f g = {!!} -- funext?
_≟_ {EQ a .a} refl p = {!!} -- need refl ≡ p which would require K

-- Questions:
-- Should enum and ∣_∣ map to a flat result or a family of results indexed by a value?

-- Enum: can tighten to a Vector later

enum : (A : U) → List (El A)
enum ZERO = []
enum ONE = tt ∷ []
enum (PLUS A B)  = map inj₁ (enum A) ++ map inj₂ (enum B)
enum (TIMES A B) = concat (map (λ a → map (λ b → (a , b)) (enum B)) (enum A))
enum (SIGMA A P) = concat (map (λ a → map (λ pa → a , pa) (enum (P a))) (enum A))
enum (PI A P) = concat (map (λ a → map (λ pa → λ b → {!!}) (enum (P a))) (enum A))
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
∣ PI A P ∣ = product (map (λ a → ∣ P a ∣) (enum A))
∣ EQ {A} a b ∣ with _≟_ {A} a b
... | yes _ = 1
... | no _ = 0

-- coherence
size-enum : ∀ (u : U) → ∣ u ∣ ≡ length (enum u)
size-enum ZERO = refl
size-enum ONE = refl
size-enum (PLUS u v) = {!!}
size-enum (TIMES u v) = {!!}
size-enum (SIGMA u P) = {!!}
size-enum (PI u P) = {!!}
size-enum (EQ {A} a b) with _≟_ {A} a b
size-enum (EQ a .a) | yes refl = refl
size-enum (EQ a b) | no ¬p = refl

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
