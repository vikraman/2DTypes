{-# OPTIONS --without-K #-}

module R where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Universe using (Universe; Indexed-universe)
open import Function renaming (_∘_ to _○_)
open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Product as C
open import Categories.Groupoid.Product as G
open import Level renaming (zero to lzero)
open import Data.Nat
open import Data.Integer as ℤ

------------------------------------------------------------------------------
-- Featherweight HoTT !

-- Each universe has:
--   * code U for types
--   * an interpretation El of these codes as semantics
--   * a semantic notion of equivalence on the interpretations
--   * possibly other semantic notions like fractional groupoids

-- The first universe (level 0) is fairly obvious

-- Once we have that level 0 universe, we can define a new universe (level 1)
-- whose codes are the equivalences at level 0. As outlined above, we then
-- define a notion of equivalence at level 1 that relates the level 0
-- equivalences.

-- We can now define a level 2 universe whose codes are the level 1
-- equivalences. We then repeat and define a notion of eqiuvalence at level 2
-- that relates the level 1 equivalences.

------------------------------------------------------------------------------
-- level 0 universe

module UNIV0 where

  infix 50 _⊕_
  infix 60 _⊗_

  data U₀ : Set where
    𝟘   : U₀
    𝟙   : U₀
    _⊕_ : U₀ → U₀ → U₀
    _⊗_ : U₀ → U₀ → U₀

  El₀ : U₀ → Set
  El₀ 𝟘         = ⊥
  El₀ 𝟙         = ⊤
  El₀ (A ⊕ B) = El₀ A ⊎ El₀ B
  El₀ (A ⊗ B) = El₀ A × El₀ B

  Univ₀ : Universe _ _
  Univ₀ = record { U = U₀ ; El = El₀ }

  -- semantic notions on Univ₀:
  -- when are interpretations equivalent

  data _≡₀_ {A : U₀} : (a b : El₀ A) → Set where
    refl₀ : (a : El₀ A) → (a ≡₀ a)

  _∼₀_ : {A B : U₀} → (f g : El₀ A → El₀ B) → Set
  _∼₀_ {A} {B} f g = (a : El₀ A) → f a ≡₀ g a

  refl∼₀ : {A B : U₀} → (f : El₀ A → El₀ B) → (f ∼₀ f)
  refl∼₀ f a = refl₀ (f a)

  record isequiv₀ {A B : U₀} (f : El₀ A → El₀ B) : Set where
    constructor mkisequiv₀
    field
      g : El₀ B → El₀ A
      α : (f ○ g) ∼₀ id
      β : (g ○ f) ∼₀ id

  _≃₀_ : (A B : U₀) → Set
  A ≃₀ B = Σ (El₀ A → El₀ B) isequiv₀

  -- example of actual equivalence of interpretations

  A⊎⊥≃A : {A : U₀} → A ⊕ 𝟘 ≃₀ A
  A⊎⊥≃A {A} = f , mkisequiv₀ g refl₀ β
    where
      f : (El₀ A ⊎ ⊥) → El₀ A
      f (inj₁ a) = a
      f (inj₂ ())

      g : El₀ A → (El₀ A ⊎ ⊥)
      g a = inj₁ a

      β : (g ○ f) ∼₀ id
      β (inj₁ a) = refl₀ (inj₁ a)
      β (inj₂ ())

  id≃₀ : {A : U₀} → A ≃₀ A
  id≃₀ = (id , mkisequiv₀ id refl₀ refl₀)

  transequiv : {A B C : U₀} → A ≃₀ B → B ≃₀ C → A ≃₀ C
  transequiv (f , mkisequiv₀ f⁻ α₁ β₁) (g , mkisequiv₀ g⁻ α₂ β₂) =
    g ○ f , mkisequiv₀ (f⁻ ○ g⁻) {!!} {!!}

------------------------------------------------------------------------------
-- level 1 universe: codes for level 0 semantic equivalence

open UNIV0

module UNIV1 where

  data _⟷_ : U₀ → U₀ → Set where
    id⟷ : {A : U₀} → A ⟷ A
    uniti₊r : {A : U₀} → A ⟷ (A ⊕ 𝟘)
    unite₊r : {A : U₀} → A ⊕ 𝟘 ⟷ A
    _◎_ :  {A B C : U₀} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)
    -- elided

  ! : {A B : U₀} → (A ⟷ B) → (B ⟷ A)
  ! unite₊r = uniti₊r
  ! uniti₊r = unite₊r
  ! id⟷ = id⟷
  ! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁

  Univ₁ : Indexed-universe _ _ _
  Univ₁ = record {
             I = U₀ × U₀
           ; U = λ { (A , B) → A ⟷ B }
           ; El = λ { { (A , B) } c → A ≃₀ B }
           }

  open Indexed-universe Univ₁ renaming (El to EL1)

  El₁ : {A B : U₀} → (c : A ⟷ B) → EL1 c
  El₁ id⟷ = {!!}
  El₁ uniti₊r = {!!}
  El₁ unite₊r = A⊎⊥≃A
  El₁ (c₁ ◎ c₂) = {!!}

  -- semantic notions on Univ₁:
  -- when are two interpretations equivalent

  record _≡₁_ {A B : U₀} {c₁ c₂ : A ⟷ B}
              (eq₁ : EL1 c₁) (eq₂ : EL1 c₂)  : Set where
    open isequiv₀ (proj₂ eq₁) renaming (g to g₁)
    open isequiv₀ (proj₂ eq₂) renaming (g to g₂)
    field
      f≡ : proj₁ eq₁ ∼₀ proj₁ eq₂
      g≡ : g₁ ∼₀ g₂

  refl≡₁ : {A B : U₀} {c : A ⟷ B} (eq : EL1 c) →
           _≡₁_ {c₁ = c} {c₂ = c} eq eq
  refl≡₁ (f , mkisequiv₀ g α β) = record {
                                    f≡ = refl∼₀ f
                                  ; g≡ = refl∼₀ g
                                  }

  _∼₁_ : {A B C D : U₀} {c₁ : A ⟷ B} {c₂ : C ⟷ D} →
         (f g : EL1 c₁ → EL1 c₂) → Set
  _∼₁_ {c₁ = c₁} {c₂ = c₂} f g =
         (eq₁ : EL1 c₁) → _≡₁_ {c₁ = c₂} {c₂ = c₂} (f eq₁) (g eq₁)

  refl∼₁ : {A B C D : U₀} {c₁ : A ⟷ B} {c₂ : C ⟷ D} →
           (f : EL1 c₁ → EL1 c₂) → (_∼₁_ {c₁ = c₁} {c₂ = c₂} f f)
  refl∼₁ f eq = refl≡₁ (f eq)

  record isequiv₁ {A B C D : U₀} {c₁ : A ⟷ B} {c₂ : C ⟷ D}
                  (f : EL1 c₁ → EL1 c₂) : Set where
    constructor mkisequiv₁
    field
      g : EL1 c₂ → EL1 c₁
      α : _∼₁_ {c₁ = c₂} {c₂ = c₂} (f ○ g) id
      β : _∼₁_ {c₁ = c₁} {c₂ = c₁} (g ○ f) id

  _≃₁_ : {A B C D : U₀} (c₁ : A ⟷ B) (c₂ : C ⟷ D) → Set
  c₁ ≃₁ c₂ = Σ (EL1 c₁ → EL1 c₂) (isequiv₁ {c₁ = c₁} {c₂ = c₂})

  -- univalence: relates level 0 equivalences with level 1 codes for these
  -- equivalences; El₁ takes us from codes to equivalences; we need a function
  -- to take us from equivalences to codes and then we need to show these two
  -- functions are inverses

  embed₀₁ : {A B : U₀} → (A ≃₀ B) → (A ⟷ B)
  embed₀₁ eq = {!!}

  record _≡₀₁_ {A B : U₀} (eq₁ eq₂ : A ≃₀ B) : Set where
    open isequiv₀ (proj₂ eq₁) renaming (g to g₁)
    open isequiv₀ (proj₂ eq₂) renaming (g to g₂)
    field
      f≡ : proj₁ eq₁ ∼₀ proj₁ eq₂
      g≡ : g₁ ∼₀ g₂

  _∼₀₁_ : {A B C D : U₀} → (f g : A ≃₀ B → C ≃₀ D) → Set
  _∼₀₁_ {A} {B} {C} {D} f g =
    (eq₁ : A ≃₀ B) → (f eq₁) ≡₀₁ (g eq₁)

  record isequiv₀₁ {A B C D : U₀} (f : A ≃₀ B → C ≃₀ D) : Set where
    constructor mkisequiv₀₁
    field
      g : C ≃₀ D → A ≃₀ B
      α : (f ○ g) ∼₀₁ id
      β : (g ○ f) ∼₀₁ id

  _≃₀₁_ : {A B C D : U₀} → A ≃₀ B → C ≃₀ D → Set
  _≃₀₁_ {A} {B} {C} {D} eq₁ eq₂ = Σ (A ≃₀ B → C ≃₀ D) isequiv₀₁

  record univalence₀₁ {A B : U₀} : Set where
    field
      α : (c : A ⟷ B) → embed₀₁ (El₁ c) ≃₁ c
      β : (eq : A ≃₀ B) → El₁ (embed₀₁ eq) ≃₀₁ eq

  -- example level 1 equivalences

  id≃₁ : {A B : U₀} (c : A ⟷ B) → c ≃₁ c
  id≃₁ c = id ,
           mkisequiv₁
             id
             (refl∼₁ {c₁ = c} {c₂ = c} id)
             (refl∼₁ {c₁ = c} {c₂ = c} id)

------------------------------------------------------------------------------
-- level 2 universe: codes for level 1 equivalences

open UNIV1

module UNIV2 where

  data _⇔_ : {A B : U₀} → (A ⟷ B) → (A ⟷ B) → Set where
    id⇔ : ∀ {A B} {c : A ⟷ B} → c ⇔ c
    _●_  : ∀ {A B} {c₁ c₂ c₃ : A ⟷ B} → (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)

  2! : {A B : U₀} {c₁ c₂ : A ⟷ B} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
  2! id⇔ = id⇔
  2! (α ● β) = (2! β) ● (2! α)

  Univ₂ : Indexed-universe _ _ _
  Univ₂ = record {
            I = Σ[ A ∈ U₀ ] Σ[ B ∈ U₀ ] (A ⟷ B) × (A ⟷ B)
          ; U = λ { (A , B , c₁ , c₂) → c₁ ⇔ c₂ }
          ; El = λ { {(A , B , c₁ , c₂)} α → c₁ ≃₁ c₂ }
          }

  open Indexed-universe Univ₂ renaming (El to EL2)

  El₂ : {A B : U₀} {c₁ c₂ : A ⟷ B} → (α : c₁ ⇔ c₂) → EL2 α
  El₂ {c₁ = c} {c₂ = .c} id⇔ = id≃₁ c
  El₂ (α₁ ● α₂) = {!!}

  -- semantic notions on Univ₂:
  -- (1) when are two interpretations equivalent

  record _≡₂_ {A B : U₀} {c₁ c₂ : A ⟷ B} {α β : c₁ ⇔ c₂}
              (eq₁ : EL2 α) (eq₂ : EL2 β) : Set where
    open isequiv₁ (proj₂ eq₁) renaming (g to g₁)
    open isequiv₁ (proj₂ eq₂) renaming (g to g₂)
    field
      f≡ : _∼₁_ {c₁ = c₁} {c₂ = c₂} (proj₁ eq₁) (proj₁ eq₂)
      g≡ : _∼₁_ {c₁ = c₂} {c₂ = c₁} g₁ g₂

  _∼₂_ : {A B C D : U₀} {c₁ c₂ : A ⟷ B} {d₁ d₂ : C ⟷ D}
         {α : c₁ ⇔ c₂} {β : d₁ ⇔ d₂} → (f g : EL2 α → EL2 β) → Set
  _∼₂_ {α = α} {β = β} f g =
    (eq : EL2 α) → _≡₂_ {α = β} {β = β} (f eq) (g eq)

  record isequiv₂ {A B C D : U₀} {c₁ c₂ : A ⟷ B} {d₁ d₂ : C ⟷ D}
         {Α : c₁ ⇔ c₂} {Β : d₁ ⇔ d₂} (f : EL2 Α → EL2 Β) : Set where
    constructor mkisequiv₂
    field
      g : EL2 Β → EL2 Α
      α : _∼₂_ {α = Β} {β = Β} (f ○ g) id
      β : _∼₂_ {α = Α} {β = Α} (g ○ f) id

  _≃₂_ : {A B C D : U₀} {c₁ c₂ : A ⟷ B} {d₁ d₂ : C ⟷ D}
         (Α : c₁ ⇔ c₂) (Β : d₁ ⇔ d₂) → Set
  Α ≃₂ Β = Σ (EL2 Α → EL2 Β) (isequiv₂ {Α = Α} {Β = Β})

  -- univalence for level 2: relates level 1 equivalences with level 2 codes for
  -- these equivalences
  -- ??

  -- (2) semantic quotients on types

  infix 40 _^_

  _^_ : {t : U₀} → (p : t ⟷ t) → (k : ℤ) → (t ⟷ t)
  p ^ (+ 0) = id⟷
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

  orderG : {t : U₀} → (p : t ⟷ t) → Groupoid (orderC p)
  orderG {U₀} p = record {
      _⁻¹ = 2!
    ; iso = λ {a} {b} {f} → record {
          isoˡ = tt
        ; isoʳ = tt
        }
    }

------------------------------------------------------------------------------
-- fractionals
-- level 3 universe: codes for level 2 quotients

open UNIV2

module UNIV3 where

  data U₃ : Set where
    # : {t : U₀} → (t ⟷ t) → U₃
    1/# : {t : U₀} → (c : t ⟷ t) → U₃
    _⊠_ : U₃ → U₃ → U₃

  Univ₃ : Universe _ _
  Univ₃ = record {
              U = U₃
            ; El = λ A → Σ[ C ∈ Category lzero lzero lzero ] (Groupoid C)
            }

  open Universe.Universe Univ₃ renaming (El to EL3)

  El₃ : (A : U₃) → EL3 A
  El₃ (# c) = _ , orderG c
  El₃ (1/# c) = {!!}
  El₃ (A ⊠ B) with El₃ A | El₃ B
  ... | (C₁ , G₁) | (C₂ , G₂) = C.Product C₁ C₂ , G.Product G₁ G₂

  -- semantic notions on Univ₃
  -- ??

------------------------------------------------------------------------------
