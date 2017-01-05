{-# OPTIONS --without-K #-}

module RF where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function renaming (_∘′_ to _○_)
open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Product as C
open import Categories.Groupoid.Product as G
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Nat hiding (_⊔_)
open import Data.Integer as ℤ hiding (_⊔_)
open import Relation.Binary.PropositionalEquality
open import Universe

------------------------------------------------------------------------------
-- Featherweight HoTT !
-- A mini language for programming with equivalences, identity types, and
-- univalence.

------------------------------------------------------------------------------
-- Some general semantic notions

-- Homotopy

_∼_ : {A B : Set} → (f g : A → B) → Set
_∼_ {A} f g = (a : A) → f a ≡ g a

refl∼ : {A B : Set} → (f : A → B) → (f ∼ f)
refl∼ f a = refl -- (f a)

sym∼ : {A B : Set} {f g : A → B} → (f ∼ g) → (g ∼ f)
sym∼ H b = sym (H b)

trans∼ : {A B : Set} {f g h : A → B} → f ∼ g → g ∼ h → f ∼ h
trans∼ p₁ p₂ a = trans (p₁ a) (p₂ a)

∼○ : {A B C : Set} {f g : A → B} {h k : B → C} →
     (f ∼ g) → (h ∼ k) → ((h ○ f) ∼ (k ○ g))
∼○ {f = f} {g = g} {h = h} H₁ H₂ x = trans (cong h (H₁ x)) (H₂ (g x))

-- Equivalence

record isequiv {A B : Set} (f : A → B) : Set where
  constructor mkisequiv
  field
    g : B → A
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

_≈_ : {A B : Set} {f : A → B} → isequiv f → isequiv f → Set
(mkisequiv g₁ _ _) ≈ (mkisequiv g₂ _ _) = g₁ ∼ g₂

refl≈ : {A B : Set} {f : A → B} → (eq : isequiv f) → eq ≈ eq
refl≈ (mkisequiv g _ _) = refl∼ g

sym≈ : {A B : Set} {f : A → B} {eq₁ eq₂ : isequiv f} →
       eq₁ ≈ eq₂ → eq₂ ≈ eq₁
sym≈ = sym∼

trans≈ : {A B : Set} {f : A → B} {eq₁ eq₂ eq₃ : isequiv f} →
       eq₁ ≈ eq₂ → eq₂ ≈ eq₃ → eq₁ ≈ eq₃
trans≈ = trans∼

_≃_ : (A B : Set) → Set
A ≃ B = Σ[ f ∈ (A → B) ] (isequiv f)

refl≃ : {A : Set} → A ≃ A
refl≃ = id , mkisequiv id (λ _ → refl) (λ _ → refl)

sym≃ : {A B : Set} → (A ≃ B) → B ≃ A
sym≃ (f , mkisequiv g α β) = g , mkisequiv f β α


trans≃ : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
trans≃ (f , mkisequiv f⁻¹ fα fβ) (g , mkisequiv g⁻¹ gα gβ) =
  g ∘ f ,
  mkisequiv (f⁻¹ ∘ g⁻¹)
            (λ x → trans (cong g (fα (g⁻¹ x))) (gα x))
            (λ x → trans (cong f⁻¹ (gβ (f x))) (fβ x))

-- Higher homotopy between functions over isequiv

_≋_ : {A B : Set} {f g : A → B} (F G : isequiv f → isequiv g) → Set
_≋_ {f = f} {g = g} F G = (eq : isequiv f) → F eq ≈ G eq

refl≋ : {A B : Set} {f g : A → B} (F : isequiv f → isequiv g) → F ≋ F
refl≋ F eq = refl≈ (F eq)

sym≋ : {A B : Set} {f g : A → B} {F G : isequiv f → isequiv g} → F ≋ G → G ≋ F
sym≋ {g = g} {F} {G} E eq = sym≈ {f = g} {eq₁ = F eq} {eq₂ = G eq} (E eq)

trans≋ : {A B : Set} {f g : A → B} {F G H : isequiv f → isequiv g} →
         F ≋ G → G ≋ H → F ≋ H
trans≋ {g = g} {F} {G} {H} E₁ E₂ eq =
  trans≈ {f = g} {eq₁ = F eq} {eq₂ = G eq} {eq₃ = H eq} (E₁ eq) (E₂ eq)

------------------------------------------------------------------------------
-- Now we move to our language

-- The universe U₀ of small types which contains:
--   * the empty type
--   * the unit type
--   * coproducts
--   * products
--   * for any type A in U₀, and any two points a and b in A, the identity type
--     ID0 a b. Note that this is recursive allowing A itself to be an identity
--     type. The identity types in this universe are all boring though.

infix 50 _⊕_
infix 60 _⊗_

-- Types: codes and interpretations

data U₀ : Set
El₀ : U₀ → Set

data U₀ where
  𝟘 : U₀
  𝟙 : U₀
  _⊕_ : U₀ → U₀ → U₀
  _⊗_ : U₀ → U₀ → U₀
  ID0 : {A : U₀} → (a₁ a₂ : El₀ A) → U₀

El₀ 𝟘 = ⊥
El₀ 𝟙 = ⊤
El₀ (A ⊕ B) = El₀ A ⊎ El₀ B
El₀ (A ⊗ B) = El₀ A × El₀ B
El₀ (ID0 a₁ a₂) = a₁ ≡ a₂

TYPE₀ : Universe _ _
TYPE₀ = record { U = U₀; El = El₀ }

-- Example

module Refl-all-the-way where

  x : El₀ (ID0 {𝟙 ⊕ 𝟙} (inj₁ tt) (inj₁ tt))
  x = refl

  -- y : El₀ (ID0 {𝟙 ⊕ 𝟙} (inj₁ tt) (inj₂ tt))
  -- ()

  z : El₀ (ID0 {ID0 {𝟙 ⊕ 𝟙} (inj₁ tt) (inj₁ tt)} refl refl)
  z = refl

------------------------------------------------------------------------------
-- Univalence for U₀

module Univalence0 where

  -- we have no identity types between types yet; we cannot even state
  -- univalence at this point. If we were to try we would need
  -- idtoeqv : {A : U₀} {a b : El₀ A} → El₀ (ID0 {A} a b) → a ≃ b
  -- but a ≃ b is non-sensical as a and b are not types

------------------------------------------------------------------------------
-- Some notions defined in U₀ that are needed to define U₁

data _⟷_ : U₀ → U₀ → Set where
  refl⟷ : {A : U₀} → A ⟷ A
  uniti₊r : {A : U₀} → A ⟷ (A ⊕ 𝟘)
  unite₊r : {A : U₀} → A ⊕ 𝟘 ⟷ A
  _◎⟷_ : {A B C : U₀} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)
  assocl₊ : {A B C : U₀} → A ⊕ (B ⊕ C) ⟷ (A ⊕ B) ⊕ C
  assocr₊ : {A B C : U₀} → (A ⊕ B) ⊕ C ⟷ A ⊕ (B ⊕ C)
  _⊕_ : {A B C D : U₀} → (A ⟷ C) → (B ⟷ D) → (A ⊕ B ⟷ C ⊕ D)
  -- new combinators for ID0; the exact list will be confirmed in the proof of
  -- univalence below
  ID0-⊤ :  ID0 {𝟙} tt tt ⟷ 𝟙
  ID0-⊕₁ : {A B : U₀} {a a' : El₀ A} →
           (ID0 {A} a a' ⟷ 𝟙) → (ID0 {A ⊕ B} (inj₁ a) (inj₁ a') ⟷ 𝟙)
  ID0-⊕₂ : {A B : U₀} {a : El₀ A} {b : El₀ B} →
           (ID0 {A ⊕ B} (inj₂ b) (inj₁ a) ⟷ 𝟘)
  ID0-⊕₃ : {A B : U₀} {a : El₀ A} {b : El₀ B} →
           (ID0 {A ⊕ B} (inj₁ a) (inj₂ b) ⟷ 𝟘)
  ID0-⊕₄ : {A B : U₀} {b b' : El₀ B} →
           (ID0 {B} b b' ⟷ 𝟙) → (ID0 {A ⊕ B} (inj₂ b) (inj₂ b') ⟷ 𝟙)
  ID0-⊗ : {A B : U₀} {a a' : El₀ A} {b b' : El₀ B} →
           (ID0 {A} a a' ⟷ 𝟙) → (ID0 {B} b b' ⟷ 𝟙) →
           (ID0 {A ⊗ B} (a , b) (a' , b') ⟷ 𝟙)
  -- need to take structure of higher paths into account explicitly
  ID0-ID : {A : U₀} {a a' : El₀ A} {p q : El₀ (ID0 {A} a a')} →
           (ID0 {ID0 {A} a a'} p q ⟷ 𝟙)
  -- elided

_∧_ : ⊤ → ⊤ → ⊤
tt ∧ tt = tt

eval : {A B : U₀} → (A ⟷ B) → El₀ A → El₀ B
eval refl⟷ = id
eval uniti₊r a = inj₁ a
eval unite₊r (inj₁ a) = a
eval unite₊r (inj₂ ())
eval (c₁ ◎⟷ c₂) = (eval c₂) ○ (eval c₁)
eval assocl₊ (inj₁ a) = inj₁ (inj₁ a)
eval assocl₊ (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
eval assocl₊ (inj₂ (inj₂ c)) = inj₂ c
eval assocr₊ (inj₁ (inj₁ a)) = inj₁ a
eval assocr₊ (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
eval assocr₊ (inj₂ c) = inj₂ (inj₂ c)
eval (c₁ ⊕ c₂) (inj₁ a) = inj₁ (eval c₁ a)
eval (c₁ ⊕ c₂) (inj₂ b) = inj₂ (eval c₂ b)
eval ID0-⊤ refl = tt
eval (ID0-⊕₁ r) refl = eval r refl
eval ID0-⊕₂ ()
eval ID0-⊕₃ ()
eval (ID0-⊕₄ r) refl = eval r refl
eval (ID0-⊗ r₁ r₂) refl = eval r₁ refl ∧ eval r₂ refl
eval ID0-ID refl = tt

data _⇔_ : {A B : U₀} → (A ⟷ B) → (A ⟷ B) → Set where
  refl⇔ : {A B : U₀} {c : A ⟷ B} → (c ⇔ c)
  _●_ : {A B : U₀} {c₁ c₂ c₃ : A ⟷ B} → (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  idl◎l : {A B : U₀} {c : A ⟷ B} → (refl⟷ ◎⟷ c) ⇔ c
  idl◎r : {A B : U₀} {c : A ⟷ B} → c ⇔ (refl⟷ ◎⟷ c)
  assocl⊕l : {A B C D E F : U₀} {c₁ : A ⟷ B} {c₂ : C ⟷ D} {c₃ : E ⟷ F} →
    ((c₁ ⊕ (c₂ ⊕ c₃)) ◎⟷ assocl₊) ⇔ (assocl₊ ◎⟷ ((c₁ ⊕ c₂) ⊕ c₃))
  assocl⊕r : {A B C D E F : U₀} {c₁ : A ⟷ B} {c₂ : C ⟷ D} {c₃ : E ⟷ F} →
    (assocl₊ ◎⟷ ((c₁ ⊕ c₂) ⊕ c₃)) ⇔ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎⟷ assocl₊)
  assocr⊕l : {A B C D E F : U₀} {c₁ : A ⟷ B} {c₂ : C ⟷ D} {c₃ : E ⟷ F} →
    (assocr₊ ◎⟷ (c₁ ⊕ (c₂ ⊕ c₃))) ⇔ (((c₁ ⊕ c₂) ⊕ c₃) ◎⟷ assocr₊)
  assocr⊕r : {A B C D E F : U₀} {c₁ : A ⟷ B} {c₂ : C ⟷ D} {c₃ : E ⟷ F} →
    (((c₁ ⊕ c₂) ⊕ c₃) ◎⟷ assocr₊) ⇔ (assocr₊ ◎⟷ (c₁ ⊕ (c₂ ⊕ c₃)))
  -- new combinators for ID1
  -- elided

2eval : {A B : U₀} {c₁ c₂ : A ⟷ B} → (c₁ ⇔ c₂) →
        isequiv (eval c₁) → isequiv (eval c₂)
2eval = hom-eq ○ 2hom
  where
  2hom : {A B : U₀} {c₁ c₂ : A ⟷ B} → (c₁ ⇔ c₂) → eval c₁ ∼ eval c₂
  2hom {c₁ = c} refl⇔ = refl∼ (eval c)
  2hom (α ● β) = trans∼ (2hom α) (2hom β)
  2hom {c₂ = c} idl◎l = refl∼ (eval c)
  2hom {c₁ = c} idl◎r = refl∼ (eval c)
  2hom (assocl⊕l {c₁ = c₁}) (inj₁ a) = refl -- (inj₁ (inj₁ (eval c₁ a)))
  2hom (assocl⊕l {c₂ = c₂}) (inj₂ (inj₁ b)) = refl -- (inj₁ (inj₂ (eval c₂ b)))
  2hom (assocl⊕l {c₃ = c₃}) (inj₂ (inj₂ c)) = refl -- (inj₂ (eval c₃ c))
  2hom (assocl⊕r {c₁ = c₁}) (inj₁ a) = refl -- (inj₁ (inj₁ (eval c₁ a)))
  2hom (assocl⊕r {c₂ = c₂}) (inj₂ (inj₁ b)) = refl -- (inj₁ (inj₂ (eval c₂ b)))
  2hom (assocl⊕r {c₃ = c₃}) (inj₂ (inj₂ c)) = refl -- (inj₂ (eval c₃ c))
  2hom (assocr⊕l {c₁ = c₁}) (inj₁ (inj₁ a)) = refl -- (inj₁ (eval c₁ a))
  2hom (assocr⊕l {c₂ = c₂}) (inj₁ (inj₂ b)) = refl -- (inj₂ (inj₁ (eval c₂ b)))
  2hom (assocr⊕l {c₃ = c₃}) (inj₂ c) = refl -- (inj₂ (inj₂ (eval c₃ c)))
  2hom (assocr⊕r {c₁ = c₁}) (inj₁ (inj₁ a)) = refl -- (inj₁ (eval c₁ a))
  2hom (assocr⊕r {c₂ = c₂}) (inj₁ (inj₂ b)) = refl -- (inj₂ (inj₁ (eval c₂ b)))
  2hom (assocr⊕r {c₃ = c₃}) (inj₂ c) = refl -- (inj₂ (inj₂ (eval c₃ c)))

  hom-eq : {A B : Set} {f g : A → B} → (f ∼ g) → isequiv f → isequiv g
  hom-eq H (mkisequiv f⁻ α β) =
    mkisequiv f⁻
      (trans∼ (∼○ (refl∼ f⁻) (sym∼ H)) α)
      (trans∼ (∼○ (sym∼ H) (refl∼ f⁻)) β)

------------------------------------------------------------------------------
-- The universe U₁ which contains:
--   * everything in U₀
--   * U₀ itself
--   * identity types: for any type A in U₁, and any two points in A, the
--     identity type ID1 a₁ a₂. Note that this is recursive allowing A itself to
--     be an identity type. The identity types in this universe are non-trivial

data U₁ : Set
El₁ : U₁ → Set

data U₁ where
  ⇑ : U₀ → U₁
  U0 : U₁
  ID1 : {A : U₁} → (a₁ a₂ : El₁ A) → U₁

El₁ (⇑ A) = El₀ A
El₁ U0 = U₀
-- any identities lifted from U₀ are trivial
El₁ (ID1 {⇑ A} a₁ a₂) = a₁ ≡ a₂
El₁ (ID1 {ID1 {ID1 {⇑ A} _ _} _ _} a b) = a ≡ b
El₁ (ID1 {ID1 {⇑ A} _ _} a b) = a ≡ b
-- identities between U₀ types are ⟷
El₁ (ID1 {U0} A B) = A ⟷ B
-- identities between ⟷ are ⇔
El₁ (ID1 {ID1 {U0} A B} c₁ c₂) = c₁ ⇔ c₂
-- identities of ⇔ is extensional
El₁ (ID1 {ID1 {ID1 {U0} A B} c₁ c₂} α β) = 2eval α ≋ 2eval β
-- after that identities are trivial again
El₁ (ID1 {ID1 {ID1 {ID1 _ _} _ _} _ _} a b) = a ≡ b

TYPE₁ : Universe _ _
TYPE₁ = record { U = U₁; El = El₁ }

------------------------------------------------------------------------------
-- Univalence for U₁

module Univalence1 where

  -- first ⟷ is complete

  postulate
    -- these are proved in pi-dual
    uniti+r≃ : {A : Set} → A ≃ (A ⊎ ⊥)
    assocl₊≃ : {A B C : Set} → (A ⊎ (B ⊎ C)) ≃ ((A ⊎ B) ⊎ C)
    _⊕≃_ : {A B C D : Set} → (A ≃ B) → (C ≃ D) → ((A ⊎ C) ≃ (B ⊎ D))

  idtoeqv : {A B : U₀} → El₁ (ID1 {U0} A B) → El₀ A ≃ El₀ B
  idtoeqv refl⟷ = refl≃
  idtoeqv uniti₊r = uniti+r≃
  idtoeqv unite₊r = sym≃ uniti+r≃
  idtoeqv (c₁ ◎⟷ c₂) = trans≃ (idtoeqv c₁) (idtoeqv c₂)
  idtoeqv assocl₊ = assocl₊≃
  idtoeqv assocr₊ = sym≃ assocl₊≃
  idtoeqv (c₁ ⊕ c₂) = (idtoeqv c₁) ⊕≃ (idtoeqv c₂)
  idtoeqv x = {!!}

  univalence : (A B : U₀) → Set
  univalence A B =  isequiv (idtoeqv {A} {B})

  univalenceP : (A B : U₀) → univalence A B
  univalenceP A B = mkisequiv comp {!!} {!!}
    where comp : {A B : U₀} → (El₀ A ≃ El₀ B) → (A ⟷ B)
          comp {𝟘} {𝟘} _ = refl⟷
          comp {𝟙} {𝟙} _ = refl⟷
          comp {ID0 {A} a₁ a₂} {ID0 {B} b₁ b₂} eq = {!!}
          comp {_} {_} eq = {!!}

  -- then ⇔ is complete

  idtoeqv2 : {A B : U₀} {P Q : El₁ (ID1 {U0} A B)} → El₁ (ID1 {(ID1 {U0} A B)} P Q) →
    isequiv (eval P) ≃ isequiv (eval Q)
  idtoeqv2 refl⇔ = refl≃
  idtoeqv2 (α ● β) = trans≃ (idtoeqv2 α) (idtoeqv2 β)
  idtoeqv2 idl◎l = {!!}
  idtoeqv2 idl◎r = {!!}
  idtoeqv2 assocl⊕l = {!!}
  idtoeqv2 assocl⊕r = {!!}
  idtoeqv2 assocr⊕l = {!!}
  idtoeqv2 assocr⊕r = {!!}

  univalence2 : {A B : U₀} (P Q : El₁ (ID1 {U0} A B)) → Set
  univalence2 {A} {B} P Q =  isequiv (idtoeqv2 {A} {B} {P} {Q})

  univalence2P : {A B : U₀} (P Q : El₁ (ID1 {U0} A B)) → univalence2 P Q
  univalence2P {A} {B} P Q = mkisequiv comp {!!} {!!}
    where comp : {A B : U₀} {c₁ c₂ : El₁ (ID1 {U0} A B)} →
                 isequiv (eval c₁) ≃ isequiv (eval c₂) → c₁ ⇔ c₂
          comp {A} {B} {c₁} {c₂} eq = {!!}

  -- idtoeqv3 as well

------------------------------------------------------------------------------
-- HITs; fractionals as  an example

------------------------------------------------------------------------------
-- Categorical semantics: We have a weak rig groupoid as shown in pi-dual
-- Here we show that we have a bicategory
-- https://en.wikipedia.org/wiki/Bicategory

-- Objects (also called 0-cells)

0-cells : Set
0-cells = U₀

-- Morphisms with fixed source and target objects (also called 1-cells)

1-cells : (A B : U₀) → Set
1-cells A B = A ⟷ B

-- Morphisms between morphisms with fixed source and target morphisms (which
-- should have themselves the same source and the same target). These are also
-- called 2-cells.

2-cells : {A B : U₀} → (c₁ c₂ : A ⟷ B) → Set
2-cells c₁ c₂ = c₁ ⇔ c₂

-- Given two objects A and B there is a category whose objects are the 1-cells
-- and morphisms are the 2-cells; the composition in this category is called
-- vertical composition.

𝔹 : (A B : U₀) → Category _ _ _
𝔹 A B = record
  { Obj = A ⟷ B
  ; _⇒_ = _⇔_
  ; _≡_ = λ α β → 2eval α ≋ 2eval β
  ; id = refl⇔
  ; _∘_ = flip _●_ -- vertical composition
  ; assoc = λ {_} {_} {_} {_} {α} {β} {γ} → assoc {α = α} {β = β} {γ = γ}
  ; identityˡ = λ {_} {_} {α} → idl {α = α}
  ; identityʳ = λ {_} {_} {α} → idr {α = α}
  ; equiv = record { refl = λ {α} → refl≋ (2eval α) ;
                     sym = λ {α} {β} E → sym≋ {F = 2eval α} {G = 2eval β} E ;
                     trans = λ {α} {β} {γ} E₁ E₂ →
                             trans≋ {F = 2eval α} {G = 2eval β} {H = 2eval γ} E₁ E₂ }
  ; ∘-resp-≡ = λ {_} {_} {_} {α} {β} {γ} {δ} E₁ E₂ →
               resp {α = α} {β = β} {γ = γ} {δ = δ} E₁ E₂
  }
  where
  idl : {A B : U₀} {c₁ c₂ : A ⟷ B} {α : c₁ ⇔ c₂} → 2eval (α ● refl⇔) ≋ 2eval α
  idl (mkisequiv g p q) b = refl

  idr : {A B : U₀} {c₁ c₂ : A ⟷ B} {α : c₁ ⇔ c₂} → 2eval (refl⇔ ● α) ≋ 2eval α
  idr (mkisequiv g p q) b = refl

  assoc : {A B : U₀} {c₁ c₂ c₃ c₄ : A ⟷ B}
        {α : c₁ ⇔ c₂} {β : c₂ ⇔ c₃} {γ : c₃ ⇔ c₄} →
        2eval (α ● (β ● γ)) ≋ 2eval ((α ● β) ● γ)
  assoc (mkisequiv g p q) b = refl

  resp : {A B : U₀} {c₁ c₂ c₃ : A ⟷ B} {α β : c₂ ⇔ c₃} {γ δ : c₁ ⇔ c₂} →
       2eval α ≋ 2eval β → 2eval γ ≋ 2eval δ →
       2eval (γ ● α) ≋ 2eval (δ ● β)
  resp E₁ E₂ (mkisequiv g p q) b = refl

-- given three objects A, B, and C there is a bifunctor * : 𝔹(B,C) × 𝔹(A,B) →
-- 𝔹(A,C) called horizontal composition; the horizontal composition is required
-- to be associative up to natural isomorphism between h*(g*f) and (h*g)*f

-- TODO

-- coherence conditions !!!

-- TODO

------------------------------------------------------------------------------
