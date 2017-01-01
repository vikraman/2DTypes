{-# OPTIONS --without-K #-}

module Univ.Syntax where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
-- open import Relation.Binary.PropositionalEquality

infixl 4 _,_
-- infixl 5 _▹_
infix 3 _↦_ _∈_ _⊢_ _∘↦_
infix 4 _⟨_⟩ _⟪_⟫
infix 2 _≣_
infix 50 _⊕_
infix 60 _⊗_
infix  30 _⟷_
infix  30 _⇔_
infixr 50 _◎_

-- types
data U : Set where
  𝟘 𝟙 : U
  _⊕_ _⊗_ : U → U → U

data _⟷_ : U → U → Set where
  id⟷ : {A : U} → A ⟷ A
  uniti₊r : {A : U} → A ⟷ (A ⊕ 𝟘)
  unite₊r : {A : U} → A ⊕ 𝟘 ⟷ A
  _◎_ : {A B C : U} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)
  -- elided

data _⇔_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  assoc◎l : ∀ {t₁ t₂ t₃ t₄} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄}
            → (c₁ ◎ (c₂ ◎ c₃)) ⇔ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : ∀ {t₁ t₂ t₃ t₄} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄}
            → ((c₁ ◎ c₂) ◎ c₃) ⇔ (c₁ ◎ (c₂ ◎ c₃))
  idl◎l   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → (id⟷ ◎ c) ⇔ c
  idl◎r   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → c ⇔ id⟷ ◎ c
  idr◎l   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → (c ◎ id⟷) ⇔ c
  idr◎r   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → c ⇔ (c ◎ id⟷)
  id⇔     : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → c ⇔ c

El : U → Set
El 𝟘       = ⊥
El 𝟙       = ⊤
El (A ⊕ B) = El A ⊎ El B
El (A ⊗ B) = El A × El B

-- contexts
data Cx : Set where
  ε : Cx
  _,_ : Cx → U → Cx
  -- _▹_ : Cx → {A B : U} → (A ⟷ B) → Cx

-- indices
data _∈_ (A : U) : Cx → Set where
  here : {Γ : Cx} → A ∈ Γ , A
  there : {Γ : Cx} {B : U} → A ∈ Γ → A ∈ Γ , B

-- terms
data _⊢_ (Γ : Cx) : U → Set where
  ⋆ : Γ ⊢ 𝟙
  inl : {A B : U} → Γ ⊢ A → Γ ⊢ A ⊕ B
  inr : {A B : U} → Γ ⊢ B → Γ ⊢ A ⊕ B
  ⟨_,_⟩ : {A B : U} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ⊗ B

eval : {A B : U} {Γ : Cx} → Γ ⊢ A → (A ⟷ B) → Γ ⊢ B
eval v id⟷ = v
eval v uniti₊r = inl v
eval (inl v) unite₊r = v
eval (inr ()) unite₊r
eval v (p ◎ q) = eval (eval v p) q

-- substitutions
data _↦_ : Cx → Cx → Set where
  -- empty
  ∅ : ε ↦ ε
  -- run a combinator
  _⟨_⟩ : {A B : U} (Γ : Cx) (p : A ⟷ B) → Γ , A ↦ Γ , B

data _≣_ : {Γ Δ : Cx} (γ δ : Γ ↦ Δ) → Set where
  ∅∅ : ∅ ≣ ∅
  _⟪_⟫ : {A B : U} {p q : A ⟷ B} (Γ : Cx) (r : p ⇔ q) → Γ ⟨ p ⟩ ≣ Γ ⟨ q ⟩

id↦ : {Γ : Cx} → Γ ↦ Γ
id↦ {ε} = ∅
id↦ {Γ , _} = Γ ⟨ id⟷ ⟩

_∘↦_ : {Γ Δ Ξ : Cx} → Δ ↦ Ξ → Γ ↦ Δ → Γ ↦ Ξ
∅ ∘↦ ∅ = ∅
Γ ⟨ p ⟩ ∘↦ .Γ ⟨ q ⟩ = Γ ⟨ q ◎ p ⟩

∘↦-assoc : {Γ Δ Ξ Ψ : Cx} {f : Γ ↦ Δ} {g : Δ ↦ Ξ} {h : Ξ ↦ Ψ}
          → (h ∘↦ g) ∘↦ f ≣ h ∘↦ (g ∘↦ f)
∘↦-assoc {f = ∅} {∅} {∅} = ∅∅
∘↦-assoc {f = Γ ⟨ p ⟩} {.Γ ⟨ q ⟩} {.Γ ⟨ r ⟩} = Γ ⟪ assoc◎l ⟫

∘↦-idl : {Γ Δ : Cx} {f : Γ ↦ Δ} → id↦ ∘↦ f ≣ f
∘↦-idl {ε} {f = ∅} = ∅∅
∘↦-idl {Γ , _} {f = .Γ ⟨ p ⟩} = Γ ⟪ idr◎l ⟫

∘↦-idr : {Γ Δ : Cx} {f : Γ ↦ Δ} → f ∘↦ id↦ ≣ f
∘↦-idr {ε} {f = ∅} = ∅∅
∘↦-idr {Γ , _} {f = .Γ ⟨ p ⟩} = Γ ⟪ idl◎l ⟫

open import Relation.Binary

≣-refl : {Γ Δ : Cx} {x : Γ ↦ Δ} → x ≣ x
≣-refl {x = ∅} = ∅∅
≣-refl {x = Γ ⟨ p ⟩} = Γ ⟪ id⇔ ⟫

≣-sym : {Γ Δ : Cx} {x y : Γ ↦ Δ} → x ≣ y → y ≣ x
≣-sym {.ε} {.ε} ∅∅ = ∅∅
≣-sym {.(Γ , _)} {.(Γ , _)} (Γ ⟪ p ⟫) = Γ ⟪ {!!} ⟫

≣-trans : {Γ Δ : Cx} {x y z : Γ ↦ Δ} → x ≣ y → y ≣ z → x ≣ z
≣-trans {.ε} {.ε} {Ξ} ∅∅ ∅∅ = ∅∅
≣-trans {.(Γ , _)} {.(Γ , _)} {Ξ} (Γ ⟪ p ⟫) (.Γ ⟪ q ⟫) = Γ ⟪ {!!} ⟫

≣-isEquiv : {Γ Δ : Cx} → IsEquivalence (_≣_ {Γ = Γ} {Δ = Δ})
≣-isEquiv = record { refl = ≣-refl ; sym = ≣-sym ; trans = ≣-trans }

open import Univ.Cats

ConCat : IsCategory Cx _↦_ _≣_
ConCat = record
          { id = id↦
          ; _∘_ = _∘↦_
          ; assoc = ∘↦-assoc
          ; identityˡ = ∘↦-idl
          ; identityʳ = ∘↦-idr
          ; equiv = ≣-isEquiv
          ; ∘-resp-≡ = {!!}
          }
