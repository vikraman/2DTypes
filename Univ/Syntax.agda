{-# OPTIONS --without-K #-}

module Univ.Syntax where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

infixl 4 _,_
infix 3 _∈_ _⊢_
infix 50 _⊕_
infix 60 _⊗_

-- types
data U : Set where
  𝟘 𝟙 : U
  _⊕_ _⊗_ : U → U → U

-- contexts
data Cx : Set where
  ε : Cx
  _,_ : Cx → U → Cx

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

-- substitutions
-- we only have empty substitutions
data _↦_ : Cx → Cx → Set where
  ∅ : {Γ : Cx} → Γ ↦ Γ

El : U → Set
El 𝟘       = ⊥
El 𝟙       = ⊤
El (A ⊕ B) = El A ⊎ El B
El (A ⊗ B) = El A × El B

open import Univ.Cats

-- trivial
ConCat : IsCategory Cx _↦_ _≡_
ConCat = record
          { id = ∅
          ; _∘_ = λ { ∅ ∅ → ∅ }
          ; assoc = λ { {f = ∅} {g = ∅} {h = ∅} → refl }
          ; identityˡ = λ { {f = ∅} → refl }
          ; identityʳ = λ { {f = ∅} → refl }
          ; equiv = isEquivalence
          ; ∘-resp-≡ = λ { refl refl → refl }
          }
