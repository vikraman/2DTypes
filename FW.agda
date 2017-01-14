module FW where

------------------------------------------------------------------------------
-- The LOGIC

-- Points and relations in universe

data Univ : Set where
  -- the universe itself
  `U : Univ
  -- points
  `𝟚 : Univ
  `f : Univ
  `t : Univ
  -- function and homotopy types
  _⟷_ : Univ → Univ → Univ
  _⇔_ : Univ → Univ → Univ
  -- (reversible) functions
  id : Univ
  not : Univ
  _∘_ : Univ → Univ → Univ
  ! : Univ → Univ
  -- homotopies
  refl⇔ : Univ
  sym⇔ : Univ → Univ
  trans⇔ : Univ → Univ → Univ
  idl : Univ
  idr : Univ
  assoc : Univ
  invr : Univ
  invl : Univ
  inv² : Univ
  ∘⇔ : Univ → Univ → Univ
  -- equivalences
  isequiv : Univ → Univ
  -- identity types
  Paths : Univ → Univ → Univ
  Freepaths : Univ → Univ
  refl : Univ
  swap : Univ
  freepath : Univ → Univ → Univ
  pathind : Univ → Univ → Univ

------------------------------------------------------------------------------
-- Judgments

-- Typability

data ⊢_∶_ : Univ → Univ → Set where
  -- elementary points
  𝟚i : ⊢ `𝟚 ∶ `U
  fi : ⊢ `f ∶ `𝟚
  ti : ⊢ `t ∶ `𝟚
  -- types of reversible functions and homotopies
  ⟷i : ⊢ (`𝟚 ⟷ `𝟚) ∶ `U
  ⇔i : ∀ {c₁ c₂} → (⊢ c₁ ∶ (`𝟚 ⟷ `𝟚)) → (⊢ c₂ ∶ (`𝟚 ⟷ `𝟚)) →
    (⊢ c₁ ⇔ c₂ ∶ `U)
  -- reversible functions
  idi : ⊢ id ∶ (`𝟚 ⟷ `𝟚)
  noti : ⊢ not ∶ (`𝟚 ⟷ `𝟚)
  ∘i : ∀ {c₁ c₂} → (⊢ c₁ ∶ (`𝟚 ⟷ `𝟚)) → (⊢ c₂ ∶ (`𝟚 ⟷ `𝟚)) →
    (⊢ c₁ ∘ c₂ ∶ (`𝟚 ⟷ `𝟚))
  !i : ∀ {c} → (⊢ c ∶ (`𝟚 ⟷ `𝟚)) → (⊢ ! c ∶ (`𝟚 ⟷ `𝟚))
  -- homotopies
  refl⇔i : ∀ {c} → ⊢ refl⇔ ∶ (c ⇔ c)
  sym⇔i : ∀ {h c₁ c₂} → (⊢ h ∶ (c₁ ⇔ c₂)) → (⊢ sym⇔ h ∶ (c₂ ⇔ c₁))
  trans⇔i : ∀ {h₁ h₂ c₁ c₂ c₃} →
    (⊢ h₁ ∶ (c₁ ⇔ c₂)) → (⊢ h₂ ∶ (c₂ ⇔ c₃)) → (⊢ trans⇔ h₁ h₂ ∶ (c₁ ⇔ c₃))
  idli : ∀ {c} → (⊢ idl ∶ ((id ∘ c) ⇔ c))
  idri : ∀ {c} → (⊢ idl ∶ ((c ∘ id) ⇔ c))
  associ : ∀ {c₁ c₂ c₃} → (⊢ assoc ∶ ((c₁ ∘ (c₂ ∘ c₃)) ⇔ ((c₁ ∘ c₂) ∘ c₃)))
  invri : ∀ {c} → (⊢ invr ∶ ((c ∘ (! c)) ⇔ id))
  invli : ∀ {c} → (⊢ invr ∶ (((! c) ∘ c) ⇔ id))
  inv²i : ∀ {c} → (⊢ inv² ∶ ((! (! c)) ⇔ c))
  ∘⇔i : ∀ {h₁ h₂ c₁ c₂ c₃ c₄} →
    (⊢ h₁ ∶ (c₁ ⇔ c₂)) → (⊢ h₂ ∶ (c₃ ⇔ c₄)) →
    (⊢ ∘⇔ h₁ h₂ ∶ ((c₁ ∘ c₃) ⇔ (c₂ ∘ c₄)))
  -- type isequiv
  isequivi : ∀ {h₁ h₂ c c₁ c₂} →
    (⊢ h₁ ∶ ((c ∘ c₁) ⇔ id)) → (⊢ h₂ ∶ ((c₂ ∘ c) ⇔ id)) →
    (⊢ isequiv c ∶ `U)
  -- identity types
  Pathsi : ∀ {A} → (⊢ A ∶ `U) → (⊢ Paths A A ∶ `U)
  Freepathsi : ∀ {A} → (⊢ A ∶ `U) → (⊢ Freepaths A ∶ `U)
  refli : ∀ {A} → (⊢ A ∶ `U) → (⊢ refl ∶ (Paths A A))
  swapi : (⊢ swap ∶ (Paths `𝟚 `𝟚))
  freepathi : ∀ {A p} → (⊢ A ∶ `U) → (⊢ p ∶ Paths A A) →
    (⊢ freepath A p ∶ Freepaths A)
  pathindi : ∀ {A p} → (⊢ A ∶ `U) → (⊢ freepath A refl ∶ Freepaths A) →
    (⊢ p ∶ Paths A A) → (⊢ pathind A p ∶ Freepaths A)

-- Judgmental equalities

data ⊢▵_▵_∶_ : Univ → Univ → Univ → Set where
  -- function inverses
  !id : ⊢▵ ! id ▵ id ∶ (`𝟚 ⟷ `𝟚)
  !not : ⊢▵ ! not ▵ not ∶ (`𝟚 ⟷ `𝟚)
  !∘ : ∀ {c₁ c₂} → ⊢▵ ! (c₁ ∘ c₂) ▵ (! c₂ ∘ ! c₁) ∶ (`𝟚 ⟷ `𝟚)

------------------------------------------------------------------------------
-- The MODEL

open import Level
open import Data.Bool

_≃_ : Set₁ → Set₁ → Set₁
A ≃ B = {!!}

id≃ : ∀ {A : Set₁} → A ≃ A
id≃ = {!!}

trans≃ : ∀ {A B C} → A ≃ B → B ≃ C → A ≃ C
trans≃ = {!!}

El : Univ → Set₁
El `U = Set
El `𝟚 = Lift Bool
El `f = {!!}
El `t = {!!}
El (A ⟷ B) = El A ≃ El B
El (A ⇔ B) = {!!}
El id = {!id≃!}
El not = {!!}
El (c₁ ∘ c₂) = {!trans≃ (El c₁) (El c₂) !}
El (! X) = {!!}
El refl⇔ = {!!}
El (sym⇔ X) = {!!}
El (trans⇔ X Y) = {!!}
El idl = {!!}
El idr = {!!}
El assoc = {!!}
El invr = {!!}
El invl = {!!}
El inv² = {!!}
El (∘⇔ X X₁) = {!!}
El (isequiv X) = {!!}
El (Paths X X₁) = {!!}
El (Freepaths X) = {!!}
El refl = {!!}
El swap = {!!}
El (freepath X X₁) = {!!}
El (pathind X X₁) = {!!}

------------------------------------------------------------------------------
