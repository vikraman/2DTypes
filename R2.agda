{-# OPTIONS --without-K #-}

module R2 where

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

------------------------------------------------------------------------------
-- Featherweight HoTT !
-- A mini language for programming with equivalences, identity types, and
-- univalence.

------------------------------------------------------------------------------
-- Semantic notions

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
-- Syntax and operational semantics

infix 50 _⊕_
infix 60 _⊗_

-- Types

data T : Set where
  𝟘   : T
  𝟙   : T
  _⊕_ : T → T → T
  _⊗_ : T → T → T

-- Combinators

data _⟷_ : T → T → Set where
  refl⟷ :    {A : T} → A ⟷ A
  uniti₊r : {A : T} → A ⟷ (A ⊕ 𝟘)
  unite₊r : {A : T} → A ⊕ 𝟘 ⟷ A
  _◎⟷_ :     {A B C : T} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)
  assocl₊ : {A B C : T} → A ⊕ (B ⊕ C) ⟷ (A ⊕ B) ⊕ C
  assocr₊ : {A B C : T} → (A ⊕ B) ⊕ C ⟷ A ⊕ (B ⊕ C)
  _⊕_     : {A B C D : T} →
            (A ⟷ C) → (B ⟷ D) → (A ⊕ B ⟷ C ⊕ D)
  -- elided

! : {A B : T} → (A ⟷ B) → (B ⟷ A)
! unite₊r = uniti₊r
! uniti₊r = unite₊r
! refl⟷ = refl⟷
! (c₁ ◎⟷ c₂) = ! c₂ ◎⟷ ! c₁
! assocl₊ = assocr₊
! assocr₊ = assocl₊
! (c₁ ⊕ c₂) = ! c₁ ⊕ ! c₂

-- Operational semantics

El : T → Set
El 𝟘       = ⊥
El 𝟙       = ⊤
El (A ⊕ B) = El A ⊎ El B
El (A ⊗ B) = El A × El B

eval : {A B : T} → (A ⟷ B) → El A → El B
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

-------------------------------------
-- Combinators between combinators --
-------------------------------------

data _⇔_ : {A B : T} → (A ⟷ B) → (A ⟷ B) → Set where
  refl⇔ : {A B : T} {c : A ⟷ B} → (c ⇔ c)
  _●_  : {A B : T} {c₁ c₂ c₃ : A ⟷ B} →
         (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  idl◎l   : {A B : T} {c : A ⟷ B} → (refl⟷ ◎⟷ c) ⇔ c
  idl◎r   : {A B : T} {c : A ⟷ B} → c ⇔ (refl⟷ ◎⟷ c)
  assocl⊕l : {A B C D E F : T}
          {c₁ : A ⟷ B} {c₂ : C ⟷ D} {c₃ : E ⟷ F} →
          ((c₁ ⊕ (c₂ ⊕ c₃)) ◎⟷ assocl₊) ⇔ (assocl₊ ◎⟷ ((c₁ ⊕ c₂) ⊕ c₃))
  assocl⊕r : {A B C D E F : T}
          {c₁ : A ⟷ B} {c₂ : C ⟷ D} {c₃ : E ⟷ F} →
          (assocl₊ ◎⟷ ((c₁ ⊕ c₂) ⊕ c₃)) ⇔ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎⟷ assocl₊)
  assocr⊕l : {A B C D E F : T}
          {c₁ : A ⟷ B} {c₂ : C ⟷ D} {c₃ : E ⟷ F} →
           (assocr₊ ◎⟷ (c₁ ⊕ (c₂ ⊕ c₃))) ⇔ (((c₁ ⊕ c₂) ⊕ c₃) ◎⟷ assocr₊)
  assocr⊕r : {A B C D E F : T}
          {c₁ : A ⟷ B} {c₂ : C ⟷ D} {c₃ : E ⟷ F} →
          (((c₁ ⊕ c₂) ⊕ c₃) ◎⟷ assocr₊) ⇔ (assocr₊ ◎⟷ (c₁ ⊕ (c₂ ⊕ c₃)))
  -- elided

2! : {A B : T} {c₁ c₂ : A ⟷ B} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
2! refl⇔ = refl⇔
2! (α ● β) = (2! β) ● (2! α)
2! idl◎l = idl◎r
2! idl◎r = idl◎l
2! assocl⊕l = assocl⊕r
2! assocl⊕r = assocl⊕l
2! assocr⊕l = assocr⊕r
2! assocr⊕r = assocr⊕l

-- Operational semantics of 2-combinators

El₂ : {A B : T} → (A ⟷ B) → Set
El₂ c = isequiv (eval c)

-- We expect that whenever c₁ ⇔ c₂ that eval c₁ ∼ eval c₂ and hence that one can
-- map from the space El₂ c₁ to El₂ c₂

2hom : {A B : T} {c₁ c₂ : A ⟷ B} → (c₁ ⇔ c₂) → eval c₁ ∼ eval c₂
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

2eval : {A B : T} {c₁ c₂ : A ⟷ B} → (c₁ ⇔ c₂) → El₂ c₁ → El₂ c₂
2eval = hom-eq ○ 2hom

------------------------------------------------------------------------------
-- Package the above in a bicategory https://en.wikipedia.org/wiki/Bicategory

-- Objects (also called 0-cells)

0-cells : Set
0-cells = T

-- Morphisms with fixed source and target objects (also called 1-cells)

1-cells : (A B : T) → Set
1-cells A B = A ⟷ B

-- Morphisms between morphisms with fixed source and target morphisms (which
-- should have themselves the same source and the same target). These are also
-- called 2-cells.

2-cells : {A B : T} → (c₁ c₂ : A ⟷ B) → Set
2-cells c₁ c₂ = c₁ ⇔ c₂

-- Given two objects A and B there is a category whose objects are the 1-cells
-- and morphisms are the 2-cells; the composition in this category is called
-- vertical composition.

idl : {A B : T} {c₁ c₂ : A ⟷ B} {α : c₁ ⇔ c₂} → 2eval (α ● refl⇔) ≋ 2eval α
idl (mkisequiv g p q) b = refl

idr : {A B : T} {c₁ c₂ : A ⟷ B} {α : c₁ ⇔ c₂} → 2eval (refl⇔ ● α) ≋ 2eval α
idr (mkisequiv g p q) b = refl

assoc : {A B : T} {c₁ c₂ c₃ c₄ : A ⟷ B}
        {α : c₁ ⇔ c₂} {β : c₂ ⇔ c₃} {γ : c₃ ⇔ c₄} →
        2eval (α ● (β ● γ)) ≋ 2eval ((α ● β) ● γ)
assoc (mkisequiv g p q) b = refl

resp : {A B : T} {c₁ c₂ c₃ : A ⟷ B} {α β : c₂ ⇔ c₃} {γ δ : c₁ ⇔ c₂} →
       2eval α ≋ 2eval β → 2eval γ ≋ 2eval δ →
       2eval (γ ● α) ≋ 2eval (δ ● β)
resp E₁ E₂ (mkisequiv g p q) b = refl

𝔹 : (A B : T) → Category _ _ _
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

-- given three objects A, B, and C there is a bifunctor * : 𝔹(B,C) × 𝔹(A,B) →
-- 𝔹(A,C) called horizontal composition; the horizontal composition is required
-- to be associative up to natural isomorphism between h*(g*f) and (h*g)*f

-- TODO

-- coherence conditions !!!

-- TODO

------------------------------------------------------------------------------





{--
record N-CELLS {u e : Level} : Set (lsuc (u ⊔ e)) where
  field
    -- codes; morphisms on codes; code category
    U : Set u
    _⟶_ : U → U → Set
    refl⟶ : {A : U} → A ⟶ A
    _◎⟶_ : {A B C : U} → (B ⟶ C) → (A ⟶ B) → (A ⟶ C)
    -- decoding a code to a space; morphisms on spaces
    Fun : (A B : U) → Set u
    idF : {A : U} → Fun A A
    _◎_ : {A B C : U} → Fun B C → Fun A B → Fun A C
--    app : {A B : U} → Fun A B → El A → El B
    -- identity of elements of spaces; homotopies; equivalences
--    refl≡ : {A : U} (a : El A) → a ≡ a
--    sym≡ : {A : U} {a b : El A} → a ≡ b → b ≡ a
--    trans≡ : {A : U} {a b c : El A} → a ≡ b → b ≡ c → a ≡ c
--    cong≡ : {A B : U} {a b : El A} → (f : Fun A B) (p : a ≡ b) → app f a ≡ app f b
    --
--    refl∼ : {A B : U} → (f : Fun A B) → (f ∼ f)
--    sym∼ : {A B : U} {f g : Fun A B} → (f ∼ g) → (g ∼ f)
--    trans∼ : {A B : U} {f g h : Fun A B} → f ∼ g → g ∼ h → f ∼ h
    --
--    _≃_ : (A B : U) → Set e
--    refl≃ : {A : U} → A ≃ A
--    sym≃ : {A B : U} → A ≃ B → B ≃ A
--    trans≃ : {A B C : U} → A ≃ B → B ≃ C → A ≃ C

------------------------------------------------------------------------------
-- 0-cells

module MOD0 where

  U : Set
  U = T

  _⟶_ : U → U → Set
  _⟶_ = _⟷_

  -- Denotations of codes

  -- The type of functions from spaces to spaces is the regular function space

  Fun : (A B : U) → Set
  Fun A B = El A → El B

  app : {A B : U} → Fun A B → El A → El B
  app f a = f a

  -- Identity

  refl≡ : {A : U} (a : El A) → a ≡ a
  refl≡ a = refl a

  sym≡ : {A : U} {a b : El A} → a ≡ b → b ≡ a
  sym≡ (refl a) = refl a

  trans≡ : {A : U} {a b c : El A} → a ≡ b → b ≡ c → a ≡ c
  trans≡ (refl a) (refl .a) = refl a

  -- Homotopy

  refl∼ : {A B : U} → (f : Fun A B) → (f ∼ f)
  refl∼ f a = refl (f a)

  sym∼ : {A B : U} {f g : Fun A B} → (f ∼ g) → (g ∼ f)
  sym∼ H b = sym≡ (H b)

  trans∼ : {A B : U} {f g h : Fun A B} → f ∼ g → g ∼ h → f ∼ h
  trans∼ p₁ p₂ a = trans≡ (p₁ a) (p₂ a)

  -- Equivalence

  _≃_ : (A B : U) → Set
  A ≃ B = Σ[ f ∈ Fun A B ] (isequiv f)

  -- Fundamental equivalences

  refl≃ : {A : U} → A ≃ A
  refl≃ = (id , mkisequiv id refl refl)

  sym≃ : {A B : U} → A ≃ B → B ≃ A
  sym≃ (f , mkisequiv g α β) = (g , mkisequiv f β α)

  trans≃ : {A B C : U} → A ≃ B → B ≃ C → A ≃ C
  trans≃ {A} {B} {C} (f , mkisequiv f⁻ α₁ β₁) (g , mkisequiv g⁻ α₂ β₂) =
    g ○ f , mkisequiv (f⁻ ○ g⁻) α β
      where α : (x : El C) → (g (f (f⁻ (g⁻ x)))) ≡ x
            α x = trans≡ (cong≡ g (α₁ (g⁻ x))) (α₂ x)
            β : (x : El A) → (f⁻ (g⁻ (g (f x)))) ≡ x
            β x = trans≡ (cong≡ f⁻ (β₂ (f x))) (β₁ x)

  -- Further examples

  A⊎⊥≃A : {A : U} → A ⊕ 𝟘 ≃ A
  A⊎⊥≃A {A} = f , mkisequiv g refl β
    where
      f : (El A ⊎ ⊥) → El A
      f (inj₁ a) = a
      f (inj₂ ())

      g : El A → (El A ⊎ ⊥)
      g a = inj₁ a

      β : (g ○ f) ∼ id
      β (inj₁ a) = refl (inj₁ a)
      β (inj₂ ())

  -- 0-cells

  0-cells : N-CELLS
  0-cells = record {
           U = U
         ; _⟶_ = _⟷_
         ; refl⟶ = refl⟷
         ; _◎⟶_ = flip _◎⟷_
         --
         ; El = El
         ; Fun = Fun
         ; eval = eval
         ; app = app
         ; idF = id
         ; _◎_ = _○_
         --
         ; _≡_ = _≡_
         ; refl≡ = refl≡
         ; sym≡ = sym≡
         ; trans≡ = trans≡
         ; cong≡ = cong≡
         --
         ; _∼_ = _∼_
         ; refl∼ = refl∼
         ; sym∼ = sym∼
         ; trans∼ = trans∼
         --
         ; isequiv = isequiv
         ; _≃_ = _≃_
         ; refl≃ = refl≃
         ; sym≃ = sym≃
         ; trans≃ = trans≃
         }

------------------------------------------------------------------------------
-- for each pair of 0-cells A and B, a category of 1-cells

module MOD1 (A B : MOD0.U) where

  open MOD0
    using    (∼○)
    renaming (Fun to Fun₀;
              refl∼ to refl∼₀; sym∼ to sym∼₀; trans∼ to trans∼₀;
              _≃_ to _≃₀_)

  -- Codes in level 1

  U : Set
  U = A ⟷ B

  -- Decoding a code to a space; the type El c is the space containing all
  -- inverses of c

  -- Functions between spaces (isequiv f₁) and (isequiv f₂). In general there
  -- may be no connection between f₁ and f₂ other that they are both from El A
  -- to El B. Ex. the types A and B might both be 1+1 and c₁ and c₂ might be id
  -- and swap.

  Fun : (c₁ c₂ : U) → Set
  Fun c₁ c₂ = El c₁ → El c₂

  idF : {c : U} → Fun c c
  idF = id

  _◎_ : {c₁ c₂ c₃ : U} → Fun c₂ c₃ → Fun c₁ c₂ → Fun c₁ c₃
  _◎_ = _○_

  app : {c₁ c₂ : U} → Fun c₁ c₂ → El c₁ → El c₂
  app F eq = F eq

  -- Identity: we have two things (g₁ , α₁ , β₁) and (g₂ , α₂ , β₂) that are
  -- both inverses of (eval c); they are the same if g₁ ∼ g₂

  data _≡_ {c : U} (eq₁ eq₂ : El c) : Set where
    refl :
      let open isequiv₀ eq₁ renaming (g to g₁)
          open isequiv₀ eq₂ renaming (g to g₂)
      in (g₁ ∼₀ g₂) → (eq₁ ≡ eq₂)

--  refl≡ : {c : U} (eq : El c) → _≡_ {c = c} eq eq
  refl≡ : {c : U} (eq : El c) → _≡_ eq eq
  refl≡ = {!!}
  refl≡ (f , mkisequiv₀ g α β) =
    record {
      f≡ = refl∼₀ f
    ; g≡ = refl∼₀ g
    }
  trans≡ : {c : U} {eq₁ eq₂ eq₃ : El c} →
           (_≡_ {c = c} eq₁ eq₂) → (_≡_ {c = c} eq₂ eq₃) →
           (_≡_ {c = c} eq₁ eq₃)
  trans≡ = {!!}
  trans≡ (record { f≡ = f≡₁ ; g≡ = g≡₁ }) (record { f≡ = f≡₂ ; g≡ = g≡₂ }) =
    record {
      f≡ = trans∼₀ f≡₁ f≡₂
    ; g≡ = trans∼₀ g≡₁ g≡₂
    }
  cong≡ : {c₁ c₂ : U} {eq₁ eq₂ : El c₁} →
   (f : Fun c₁ c₂) → _≡_ {c = c₁} eq₁ eq₂ →
   _≡_ {c = c₂} (app {c₁ = c₁} {c₂ = c₂} f eq₁) (app {c₁ = c₁} {c₂ = c₂} f eq₂)
  cong≡ = {!!}
  cong≡ {eq₁ = (f₁ , mkisequiv₀ g₁ α₁ β₁)}
        {eq₂ = (f₂ , mkisequiv₀ g₂ α₂ β₂)}
        (F , G , γ , δ)
        (record { f≡ = f≡ ; g≡ = g≡ }) =
    record {
       f≡ = trans∼₀ (γ f₁) (trans∼₀ f≡ (sym∼₀ (γ f₂)))
     ; g≡ = trans∼₀ (δ g₁) (trans∼₀ g≡ (sym∼₀ (δ g₂)))
     }

  -- Homotopy

  _∼_ : {c₁ c₂ : U} → (f g : Fun c₁ c₂) → Set
  _∼_ {c₁ = c₁} {c₂ = c₂} f g =
    (eq : El c₁) →
    _≡_ {c = c₂} (app {c₁ = c₁} {c₂ = c₂} f eq) (app {c₁ = c₁} {c₂ = c₂} g eq)

  refl∼ : {c : U} → (f : Fun c c) →
          _∼_ {c₁ = c} {c₂ = c} f f
  refl∼ {c = c} f eq = refl≡ (app {c₁ = c} {c₂ = c} f eq)

  -- Equivalence

  record isequiv {c₁ c₂ : U}
         (f : Fun c₁ c₂) : Set where
    constructor mkisequiv
    field
      g : Fun c₂ c₁
      α : _∼_ {c₁ = c₂} {c₂ = c₂} (f ○ g) (idF {c = c₂})
      β : _∼_ {c₁ = c₁} {c₂ = c₁} (g ○ f) idF

  _≃_ : (c₁ c₂ : U) → Set
  _≃_ c₁ c₂ = Σ (Fun c₁ c₂) (isequiv {c₁ = c₁} {c₂ = c₂})

  -- Example level 1 equivalences

  refl≃ : (c : U) → c ≃ c
  refl≃ c = idF {c = c},
          mkisequiv
            (idF {c = c})
            (refl∼ {c = c} (idF {c = c}))
            (refl∼ {c = c} (idF {c = c}))

  -- the proofs below need trans∼ and inv∼, but then are straightforward.

  trans≃ : {c₁ c₂ c₃ : U} → (c₁ ≃ c₂) → (c₂ ≃ c₃) → (c₁ ≃ c₃)
  trans≃ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}
    (f , mkisequiv f⁻ α₁ β₁) (g , mkisequiv g⁻ α₂ β₂) =
    g ○ f , mkisequiv (f⁻ ○ g⁻)
    (λ eq₁ → {!!})
    (λ eq₂ → {!!})

  -- Universe 1

  Univ : N-CELLS
  Univ = record {
               U = A ⟷ B
             ; _⟷_ = _⇔_
             ; refl⟷ = refl⇔
             ; _◎⟷_ = flip _●_
             ; El = λ _ → A ≃₀ B
             ; Fun = Fun
             ; idF = λ {c} → idF {c = c}
             ; app = {!!} -- λ {c₁} {c₂} → app {c₁ = c₁} {c₂}
             ; _◎_ = _○_
             ; _≡_ = {!!} -- λ { {c} → _≡_ {c = c}}
             ; _∼_ = λ { {c₁} {c₂} → _∼_ {c₁ = c₁} {c₂ = c₂}}
             ; _≃_ = _≃_
             ; refl≡ = {!!} -- refl≡
             ; sym≡ = {!!}
             ; trans≡ = {!!} -- trans≡
             ; cong≡ = {!!} -- cong≡
             ; refl∼ = {!!} -- refl∼
             ; sym∼ = {!!}
             ; trans∼ = {!!}
             ; refl≃ = {!!}
             ; sym≃ = {!!}
             ; trans≃ = {!!}
             }

------------------------------------------------------------------------------
-- level 0-1 cross equivalences

module MOD0x1 where

  open MOD0
    using (A⊎⊥≃A)
    renaming (U to U₀; _∼_ to _∼₀_;
              _≃_ to _≃₀_; mkisequiv to mkisequiv₀;
              refl≃ to refl≃₀; sym≃ to sym≃₀; trans≃ to trans≃₀)

  open MOD1
    using    ()
    renaming (U to U₁; El to El₁; _≡_ to _≡₁_; _≃_ to _≃₁_)

  -- We want to make sure that the 1-cells are exactly the equivalences between
  -- 0-cells. We will define a cross-level equivalence between them: that is
  -- univalence!

  sound : {A B : U₀} → (c : U₁ A B) → El₁ A B c
  sound refl⟷ = {!!} -- refl≃₀
  sound uniti₊r = {!!} -- sym≃₀ A⊎⊥≃A
  sound unite₊r = {!!} -- A⊎⊥≃A
  sound (c₁ ◎⟷ c₂) = {!!} -- trans≃₀ (sound c₁) (sound c₂)
  sound assocl₊ = {!!}
  sound assocr₊ = {!!}

  -- The two spaces in question are:
  -- A ≃₀ B in level 0 universe, and
  -- A ⟷ B in level 1 universe
  -- We need functions going in both directions that are inverses
  -- from A ⟷ B to A ≃₀ B we have the function sound in MOD1
  -- from A ≃₀ B to A ⟷ B we have the function complete below

  complete : {A B : U₀} → (A ≃₀ B) → (A ⟷ B)
  complete {A} {B} (f , mkisequiv₀ g α β) = {!!}

  -- Now we need to require inverses

  record univalence {A B : U₀} : Set where
--    field
--      α : (c : A ⟷ B) → _≃₁_ A B (complete (sound c)) c
--      β : (eq : A ≃₀ B) → Σ[ c ∈ A ⟷ B ] _≡₁_ A B {c = c} (sound (complete eq)) eq

------------------------------------------------------------------------------
-- level 2 universe: codes for level 1 equivalences

module MOD2 where

  open MOD0
    using ()
    renaming (U to U₀)

  open MOD1
    using (_⟷_; refl⟷; _◎_; !)
    renaming (app to app₁; _∼_ to _∼₁_;
              _≃_ to _≃₁_; refl≃ to refl≃₁; trans≃ to trans≃₁)

  -- Codes in level 2 for level 1 equivalences

  -- Decoding a code to a space

  El : {A B : U₀} {c₁ c₂ : A ⟷ B} → (α : c₁ ⇔ c₂) → Set
  El {c₁ = c₁} {c₂ = c₂} _ = c₁ ≃₁ c₂

  -- Every code at level 2 does correspond to a level 1 equivalence
  -- Reverse direction is univalence; addressed below

  sound : {A B : U₀} {c₁ c₂ : A ⟷ B} → (α : c₁ ⇔ c₂) → El α
  sound {c₁ = c} {c₂ = .c} refl⇔ = refl≃₁ c
  sound (α₁ ● α₂) = trans≃₁ (sound α₁) (sound α₂)

  -- Type of functions

  Fun : {A B : U₀} {c₁ c₂ : A ⟷ B} → (α β : c₁ ⇔ c₂) → Set
  Fun {A} {B} {c₁} {c₂} α β = {!!}

  app : {A B : U₀} {c₁ c₂ : A ⟷ B} {α β : c₁ ⇔ c₂} → Fun α β → El α → El β
  app {A} {B} {c₁} {c₂} {α} {β} f eq = {!!}

  idF : {A B : U₀} {c₁ c₂ : A ⟷ B} {α : c₁ ⇔ c₂} → Fun α α
  idF = {!!}

  compose : {A B : U₀} {c₁ c₂ : A ⟷ B} {α β γ : c₁ ⇔ c₂} →
            (f : Fun α β) (g : Fun β γ) → Fun α γ
  compose = {!!}

  -- semantic notions on Univ₂:
  -- (1) when are two interpretations equivalent

  record _≡_ {A B : U₀} {c₁ c₂ : A ⟷ B} {α : c₁ ⇔ c₂}
              (eq₁ eq₂ : El α) : Set where
    open MOD1.isequiv (proj₂ eq₁) renaming (g to g₁)
    open MOD1.isequiv (proj₂ eq₂) renaming (g to g₂)
    field
      f≡ : _∼₁_ {c₁ = c₁} {c₂ = c₂} (proj₁ eq₁) (proj₁ eq₂)
      g≡ : _∼₁_ {c₁ = c₂} {c₂ = c₁} g₁ g₂

  _∼_ : {A B : U₀} {c₁ c₂ : A ⟷ B} {α β : c₁ ⇔ c₂} (f g : Fun α β) → Set
  _∼_ {α = α} {β = β} f g =
      (eq : El α) → _≡_ {α = β} (app f eq) (app g eq)

  record _≃_ {A B : U₀} {c₁ c₂ : A ⟷ B} (α β : c₁ ⇔ c₂) : Set where
    constructor eq
    field
      f : Fun α β
      g : Fun β α
      for : _∼_ {α = α} (compose g f) idF
      bck : _∼_ {α = β} (compose f g) idF

  -- univalence for level 2: relates level 1 equivalences with level 2 codes for
  -- these equivalences
  -- ??

  -- (2) semantic quotients on types

  infix 40 _^_

  _^_ : {t : U₀} → (p : t ⟷ t) → (k : ℤ) → (t ⟷ t)
  p ^ (+ 0) = refl⟷
  p ^ (+ (suc k)) = p ◎ (p ^ (+ k))
  p ^ -[1+ 0 ] = ! p
  p ^ (-[1+ (suc k) ]) = (! p) ◎ (p ^ -[1+ k ])

  record Iter {t : U₀} (p : t ⟷ t) : Set where
    constructor <_,_,_>
    field
      k : ℤ
      q : t ⟷ t
      α : q ⇔ p ^ k

  orderC : {t : U₀} → (t ⟷ t) → Category lzero lzero lzero
  orderC p = record {
     Obj = Iter p
   ; _⇒_ = λ p^i p^j → Iter.q p^i ⇔ Iter.q p^j
   ; _≡_ = λ _ _ → ⊤
   ; id  = refl⇔
   ; _∘_ = flip _●_
   ; assoc = tt
   ; identityˡ = tt
   ; identityʳ = tt
   ; equiv = record
     { refl = tt
     ; sym = λ _ → tt
     ; trans = λ _ _ → tt
     }
   ; ∘-resp-≡ = λ _ _ → tt
   }

  orderG : {t : U₀} → (p : t ⟷ t) → Groupoid (orderC p)
  orderG {U₀} p = record {
      _⁻¹ = 2!
    ; iso = λ {a} {b} {f} → record {
          isoˡ = tt
        ; isoʳ = tt
        }
    }

  -- Universe 2

  Univ : {A B : U₀} (c₁ c₂ : A ⟷ B) → N-CELLS
  Univ c₁ c₂ = record {
             U = c₁ ⇔ c₂
           ; El = El
           ; Fun = Fun
           ; app = {!!}
           ; _◎_ = {!!}
           ; _≡_ = {!!}
           ; _∼_ = {!!}
           ; _≃_ = {!!}
           ; refl≡ = {!!}
           ; sym≡ = {!!}
           ; trans≡ = {!!}
           ; cong≡ = {!!}
           ; refl∼ = {!!}
           ; sym∼ = {!!}
           ; trans∼ = {!!}
           ; refl≃ = {!!}
           ; sym≃ = {!!}
           ; trans≃ = {!!}
           }

------------------------------------------------------------------------------
-- level 1-2 cross equivalences

module MOD1x2 where

  open MOD0
    using    ()
    renaming (U to U₀)

  open MOD1
    using    (_⟷_)
    renaming (_≃_ to _≃₁_)

  open MOD2
    using    (_⇔_; sound)
    renaming (_≡_ to _≡₂_; _≃_ to _≃₂_)

  -- We want to make sure that the level 2 codes are exactly the level 1
  -- equivalences. We will define a cross-level equivalence between them: that
  -- is univalence!

  complete : {A B : U₀} {c₁ c₂ : A ⟷ B} → (c₁ ≃₁ c₂) → (c₁ ⇔ c₂)
  complete = {!!}

  record univalence {A B : U₀} {c₁ c₂ : A ⟷ B} : Set where
    field
      α : (α : c₁ ⇔ c₂) → complete (sound α) ≃₂ α
      β : (eq : c₁ ≃₁ c₂) → Σ[ α ∈ c₁ ⇔ c₂ ] _≡₂_ (sound (complete eq)) eq

------------------------------------------------------------------------------
-- Fractionals
-- level 3 universe: codes for level 2 quotients

module MOD3 where

  open MOD0
    using ()
    renaming (U to U₀)

  open MOD1
    using (_⟷_)
    renaming ()

  open MOD2
    using (orderG)
    renaming ()

  -- Codes for level 3 are HIT corresponding to level 2 fractional groupoids

  data U : Set where
    # : {t : U₀} → (t ⟷ t) → U
    1/# : {t : U₀} → (c : t ⟷ t) → U
    _⊠_ : U → U → U

  -- Each code denotes a groupoid

  El : U → Set₁
  El = λ A → Σ[ C ∈ Category lzero lzero lzero ] (Groupoid C)

  sound : (A : U) → El A
  sound (# c) = _ , orderG c
  sound (1/# c) = {!!}
  sound (A ⊠ B) with sound A | sound B
  ... | (C₁ , G₁) | (C₂ , G₂) = C.Product C₁ C₂ , G.Product G₁ G₂

  -- Type of functions

  Fun : (A B : U) → Set
  Fun A B = {!!}

  -- Identity

  -- Homotopy

  -- Equivalence

  Univ₃ : N-CELLS
  Univ₃ = record {
            U = U
          ; El = El
          ; Fun = Fun
          ; app = {!!}
          ; _◎_ = {!!}
          ; _≡_ = {!!}
          ; _∼_ = {!!}
          ; _≃_ = {!!}
          ; refl≡ = {!!}
          ; sym≡ = {!!}
          ; trans≡ = {!!}
          ; cong≡ = {!!}
          ; refl∼ = {!!}
          ; sym∼ = {!!}
          ; trans∼ = {!!}
          ; refl≃ = {!!}
          ; sym≃ = {!!}
          ; trans≃ = {!!}
          }

------------------------------------------------------------------------------
--}
