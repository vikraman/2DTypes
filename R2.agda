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
open import Universe

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

--

_≃_ : (A B : Set) → Set
A ≃ B = Σ[ f ∈ (A → B) ] (isequiv f)

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
-- Universe of types (following Appendix 2 in HoTT book)
-- Univalence, Fractionals, and HITs

-- We have two universes U₀ (called T above) and U₁
-- U₀ contains the small types
-- Everything in U₀ is also in U₁ and U₀ itself is in U₁
-- Identity types only in U₁ because they are boring in U₀

mutual

  U₀ : Set
  U₀ = T

  El₀ : U₀ → Set
  El₀ = El

  data U₁ : Set where
    LIFT : U₀ → U₁
    U0 : U₁
    ID : (A B : U₀) → U₁
    ID2 : {A B : U₀} → (P Q : El₁ (ID A B)) → U₁
    -- could have ID3 and so on
    # : {A : U₀} → El₁ (ID A A) → U₁
    1/# : {A : U₀} → El₁ (ID A A) → U₁
    _⊠_ : U₁ → U₁ → U₁

  infix 40 _^_

  _^_ : {A : T} → (p : A ⟷ A) → (k : ℤ) → (A ⟷ A)
  p ^ (+ 0) = refl⟷
  p ^ (+ (suc k)) = p ◎⟷ (p ^ (+ k))
  p ^ -[1+ 0 ] = ! p
  p ^ (-[1+ (suc k) ]) = (! p) ◎⟷ (p ^ -[1+ k ])

  record Iter {A : T} (p : A ⟷ A) : Set where
    constructor <_,_,_>
    field
      k : ℤ
      q : A ⟷ A
      α : q ⇔ p ^ k

  orderC : {A : T} → (A ⟷ A) → Category lzero lzero lzero
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

  orderG : {A : T} → (p : A ⟷ A) → Groupoid (orderC p)
  orderG {U₀} p = record {
      _⁻¹ = 2!
    ; iso = λ {a} {b} {f} → record {
          isoˡ = tt
        ; isoʳ = tt
        }
    }

  El₁ : U₁ → Set
  El₁ (LIFT A) = El A
  El₁ U0 = U₀
  El₁ (ID A B) = A ⟷ B
  El₁ (ID2 P Q) = P ⇔ Q
  El₁ (# P) = {!!} -- something with orderG
  El₁ (1/# P) = {!!}
  El₁ (A ⊠ B) = {!!}

idtoeqv : {A B : U₀} → El₁ (ID A B) → El₀ A ≃ El₀ B
idtoeqv refl⟷ = id , mkisequiv id {!!} {!!}
idtoeqv uniti₊r = {!!}
idtoeqv unite₊r = {!!}
idtoeqv (c₁ ◎⟷ c₂) = {!!}
idtoeqv assocl₊ = {!!}
idtoeqv assocr₊ = {!!}
idtoeqv (c₁ ⊕ c₂) = {!!}

univalence : (A B : U₀) → Set
univalence A B =  isequiv (idtoeqv {A} {B})

univalenceP : (A B : U₀) → univalence A B
univalenceP A B = mkisequiv {!!} {!!} {!!}

--

idtoeqv2 : {A B : U₀} {P Q : El₁ (ID A B)} → El₁ (ID2 P Q) → El₂ P ≃ El₂ Q
idtoeqv2 refl⇔ = {!!}
idtoeqv2 (α ● β) = {!!}
idtoeqv2 idl◎l = {!!}
idtoeqv2 idl◎r = {!!}
idtoeqv2 assocl⊕l = {!!}
idtoeqv2 assocl⊕r = {!!}
idtoeqv2 assocr⊕l = {!!}
idtoeqv2 assocr⊕r = {!!}

univalence2 : {A B : U₀} (P Q : El₁ (ID A B)) → Set
univalence2 {A} {B} P Q =  isequiv (idtoeqv2 {A} {B} {P} {Q})

univalence2P : {A B : U₀} (P Q : El₁ (ID A B)) → univalence2 P Q
univalence2P {A} {B} P Q = mkisequiv {!!} {!!} {!!}

------------------------------------------------------------------------------
