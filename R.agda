{-# OPTIONS --without-K #-}

module R where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Universe
open import Function renaming (_∘_ to _○_)
open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Product as C
open import Categories.Groupoid.Product as G
open import Level renaming (zero to lzero)
open import Data.Nat
open import Data.Integer as ℤ

infix 4 _≃_
infix 4 _≋_
infix 40 _^_
infixr 50 _◎_
infix 50 _⊕_
infix 50 _⊠_
infix 60 _⊗_
infixr 60 _●_

------------------------------------------------------------------------------
-- level 0 types: codes, universe, homotopies, and equivalences

-- codes for level 0 types

data τ : Set where
  𝟘 : τ
  𝟙 : τ
  _⊕_ : τ → τ → τ
  _⊗_ : τ → τ → τ

-- level 0 types are discrete groupoids

τ-univ : Universe _ _
τ-univ = record { U = τ ; El = ⟦_⟧ }
  where ⟦_⟧ : τ → Set
        ⟦ 𝟘 ⟧ = ⊥
        ⟦ 𝟙 ⟧ = ⊤
        ⟦ t₁ ⊕ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
        ⟦ t₁ ⊗ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

-- the only relation on elements of discrete groupoids is ≡

data _≡_ {A : Set} : (a b : A) → Set where
  refl : (a : A) → (a ≡ a)

-- homotopy: functions between level 0 types are not dependent
-- equality of elements is trivial

_∼_ : {A B : Set} → (f g : A → B) → Set
_∼_ {A} {B} f g = (x : A) → f x ≡ g x

-- equivalence of level 0 types

record isequiv {A B : Set} (f : A → B) : Set where
  constructor mkisequiv
  field
    g : B → A
    α : (f ○ g) ∼ id
    h : B → A
    β : (h ○ f) ∼ id

_≃_ : (A B : Set) → Set
A ≃ B = Σ (A → B) isequiv

-- example of actual equivalences

A⊎⊥≃A : {A : Set} → (A ⊎ ⊥) ≃ A
A⊎⊥≃A {A} = f , mkisequiv g α g β
  where
    f : (A ⊎ ⊥) → A
    f (inj₁ a) = a
    f (inj₂ ())

    g : A → (A ⊎ ⊥)
    g a = inj₁ a

    α : (f ○ g) ∼ id
    α a = refl a

    β : (g ○ f) ∼ id
    β (inj₁ a) = refl (inj₁ a)
    β (inj₂ ())

idequiv : {A : Set} → A ≃ A
idequiv = (id , mkisequiv id refl id refl)

transequiv : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
transequiv (f , feq) (g , geq) = {!!}

------------------------------------------------------------------------------
-- codes for equivalences; univalence

-- we have a higher universe whose elements are codes for equivalences in the
-- level 0 universe

data _⟷_ : τ → τ → Set where
  id⟷ : {t : τ} → t ⟷ t
  uniti₊r : {t : τ} → t ⟷ (t ⊕ 𝟘)
  unite₊r : {t : τ} → t ⊕ 𝟘 ⟷ t
  _◎_ :  {t₁ t₂ t₃ : τ} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  -- elided

! : {t₁ t₂ : τ} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
! unite₊r = uniti₊r
! uniti₊r = unite₊r
! id⟷ = id⟷
! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁

T-univ : Indexed-universe _ _ _
T-univ = record {
           I = τ × τ
         ; U = λ { (t₁ , t₂) → t₁ ⟷ t₂ }
         ; El = λ { {(t₁ , t₂)} c → Universe.El τ-univ t₁ ≃ Universe.El τ-univ t₂ }
         }

⟦_⟧ : {t₁ t₂ : τ} → (c : t₁ ⟷ t₂) → Indexed-universe.El T-univ {(t₁ , t₂)} c
⟦ id⟷ ⟧ = {!!}
⟦ uniti₊r ⟧ = {!!}
⟦ unite₊r ⟧ = A⊎⊥≃A
⟦ c₁ ◎ c₂ ⟧ = {!!}

-- now we need to specify what it means for two equivalences to be the same

record _≋_ {A B : Set} (eq₁ eq₂ : A ≃ B) : Set where
  constructor eq
  open isequiv (proj₂ eq₁) renaming (g to g₁)
  open isequiv (proj₂ eq₂) renaming (g to g₂)
  field
    f≡ : proj₁ eq₁ ∼ proj₁ eq₂
    g≡ : g₁ ∼ g₂

-- homotopy at level 1

_∼₁_ : {A B C D : Set} → (f g : A ≃ B → C ≃ D) → Set
_∼₁_ {A} {B} {C} {D} f g = (eq : A ≃ B) → f eq ≋ g eq

-- equivalences at level 1

record isequiv₁ {A B C D : Set} (f : A ≃ B → C ≃ D) : Set where
  constructor mkisequiv₁
  field
    g : C ≃ D → A ≃ B
    α : (f ○ g) ∼₁ id
    h : C ≃ D → A ≃ B
    β : (h ○ f) ∼ id

_≃₁_ : {A B C D : Set} → (A≃B C≃D : Set) → Set
_≃₁_ {A} {B} {C} {D} A≃B C≃D = Σ (A ≃ B → C ≃ D) isequiv₁

------------------------------------------------------------------------------
-- codes for equivalences of equivalences

data _⇔_ : {t₁ t₂ : τ} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  id⇔ : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → c ⇔ c
  _●_  : ∀ {t₁ t₂} {c₁ c₂ c₃ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)

2! : {t₁ t₂ : τ} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
2! id⇔ = id⇔
2! (α ● β) = (2! β) ● (2! α)

TT-univ : Indexed-universe _ _ _
TT-univ = record {
            I = Σ[ t₁ ∈ τ ] Σ[ t₂ ∈ τ ] (t₁ ⟷ t₂) × (t₁ ⟷ t₂)
          ; U = λ { (t₁ , t₂ , c₁ , c₂) → c₁ ⇔ c₂ }
          ; El = λ { {(t₁ , t₂ , c₁ , c₂)} α → c₁ ⇔ c₂ }
          }

-- once we complete the entire set of _⟷_ we will have the following situation:
-- the space A ⊕ A ≃ A ⊕ A contains the following elements:
-- id≃
-- swap≃
-- these two elements should not be identified
-- in the world of codes these elements are represented by different codes
-- id⟷ and swap₊
-- the relation ⇔ tells us which codes can be identified and it does NOT identify
-- id⟷ and swap₊

------------------------------------------------------------------------------
-- fractionals

_^_ : {t : τ} → (p : t ⟷ t) → (k : ℤ) → (t ⟷ t)
p ^ (+ 0) = id⟷
p ^ (+ (suc k)) = p ◎ (p ^ (+ k))
p ^ -[1+ 0 ] = ! p
p ^ (-[1+ (suc k) ]) = (! p) ◎ (p ^ -[1+ k ])

record Iter {t : τ} (p : t ⟷ t) : Set where
  constructor <_,_,_>
  field
    k : ℤ
    q : t ⟷ t
    α : q ⇔ p ^ k

data τ/ : Set where
  # : {t : τ} → (t ⟷ t) → τ/
  1/# : {t : τ} → (c : t ⟷ t) → τ/
  _⊠_ : τ/ → τ/ → τ/

orderC : {t : τ} → (t ⟷ t) → Category lzero lzero lzero
orderC p = record {
   Obj = Iter p
 ; _⇒_ = λ p^i p^j → Iter.q p^i ⇔ Iter.q p^j
 ; _≡_ = λ _ _ → ⊤
 ; id  = id⇔
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

orderG : {t : τ} → (p : t ⟷ t) → Groupoid (orderC p)
orderG {τ} p = record {
    _⁻¹ = 2!
  ; iso = λ {a} {b} {f} → record {
        isoˡ = tt
      ; isoʳ = tt
      }
  }

τ/-univ : Universe _ _
τ/-univ = record {
            U = τ/
          ; El = λ t/ → Σ[ C ∈ Category lzero lzero lzero ] (Groupoid C)
          }

⟦_⟧/ : (t/ : τ/) → Universe.El τ/-univ t/
⟦ # c ⟧/ = _ , orderG c
⟦ 1/# c ⟧/ = {!!}
⟦ T₁ ⊠ T₂ ⟧/ with ⟦ T₁ ⟧/ | ⟦ T₂ ⟧/
... | (C₁ , G₁) | (C₂ , G₂) = C.Product C₁ C₂ , G.Product G₁ G₂

------------------------------------------------------------------------------
