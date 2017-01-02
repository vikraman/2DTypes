{-# OPTIONS --without-K #-}

module Univ.Syntax where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

infixl 4 _,_
-- infixl 5 _▹_
infix 3 _↦_ _∈_ _⊢_ _∘↦_
infix 4 _⟨_⟩ _⟪_⟫
infix 2 _≣_

open import Univ.Pi

-- contexts
data Con (U : Set) : Set where
  ε : Con U
  _,_ : Con U → U → Con U
  -- _▹_ : Con U → {A B : U} → (A ⟷ B) → Con U

-- indices
data _∈_ {U : Set} (A : U) : Con U → Set where
  here : {Γ : Con U} → A ∈ Γ , A
  there : {Γ : Con U} {B : U} → A ∈ Γ → A ∈ Γ , B

-- contexts on 𝒰
Cx : Set
Cx = Con 𝒰

-- terms
data _⊢_ (Γ : Cx) : 𝒰 → Set where
  ⋆ : Γ ⊢ 𝟙
  inl : {A B : 𝒰} → Γ ⊢ A → Γ ⊢ A ⊕ B
  inr : {A B : 𝒰} → Γ ⊢ B → Γ ⊢ A ⊕ B
  ⟨_,_⟩ : {A B : 𝒰} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ⊗ B

ap : {A B : 𝒰} {Γ : Cx} → Γ ⊢ A → (A ⟷ B) → Γ ⊢ B
ap (inl ()) unite₊l
ap (inr v) unite₊l = v
ap v uniti₊l = inr v
ap (inl v) unite₊r = v
ap (inr ()) unite₊r
ap ⋆ uniti₊r = inl ⋆
ap (inl v) uniti₊r = inl (inl v)
ap (inr v) uniti₊r = inl (inr v)
ap ⟨ v , w ⟩ uniti₊r = inl ⟨ v , w ⟩
ap (inl v) swap₊ = inr v
ap (inr v) swap₊ = inl v
ap (inl v) assocl₊ = inl (inl v)
ap (inr (inl v)) assocl₊ = inl (inr v)
ap (inr (inr v)) assocl₊ = inr v
ap (inl (inl v)) assocr₊ = inl v
ap (inl (inr v)) assocr₊ = inr (inl v)
ap (inr v) assocr₊ = inr (inr v)
ap ⟨ v , w ⟩ unite⋆l = w
ap v uniti⋆l = ⟨ ⋆ , v ⟩
ap ⟨ v , w ⟩ unite⋆r = v
ap v uniti⋆r = ⟨ v , ⋆ ⟩
ap ⟨ v , w ⟩ swap⋆ = ⟨ w , v ⟩
ap ⟨ v , ⟨ w , u ⟩ ⟩ assocl⋆ = ⟨ ⟨ v , w ⟩ , u ⟩
ap ⟨ ⟨ v , w ⟩ , u ⟩ assocr⋆ = ⟨ v , ⟨ w , u ⟩ ⟩
ap ⟨ () , w ⟩ absorbr
ap ⟨ v , () ⟩ absorbl
ap ⟨ inl v , w ⟩ dist = inl ⟨ v , w ⟩
ap ⟨ inr v , w ⟩ dist = inr ⟨ v , w ⟩
ap (inl ⟨ v , w ⟩) factor = ⟨ inl v , w ⟩
ap (inr ⟨ v , w ⟩) factor = ⟨ inr v , w ⟩
ap ⟨ v , inl w ⟩ distl = inl ⟨ v , w ⟩
ap ⟨ v , inr w ⟩ distl = inr ⟨ v , w ⟩
ap (inl ⟨ v , w ⟩) factorl = ⟨ v , inl w ⟩
ap (inr ⟨ v , w ⟩) factorl = ⟨ v , inr w ⟩
ap v id⟷ = v
ap v (p ◎ q) = ap (ap v p) q
ap (inl v) (p ⊕ q) = inl (ap v p)
ap (inr v) (p ⊕ q) = inr (ap v q)
ap ⟨ v , w ⟩ (p ⊗ q) = ⟨ ap v p , ap w q ⟩

-- substitutions
data _↦_ : Cx → Cx → Set where
  -- empty
  ∅ : ε ↦ ε
  -- run a combinator
  _⟨_⟩ : {A B : 𝒰} (Γ : Cx) (p : A ⟷ B) → Γ , A ↦ Γ , B

data _≣_ : {Γ Δ : Cx} (γ δ : Γ ↦ Δ) → Set where
  ∅∅ : ∅ ≣ ∅
  _⟪_⟫ : {A B : 𝒰} {p q : A ⟷ B} (Γ : Cx) (r : p ⇔ q) → Γ ⟨ p ⟩ ≣ Γ ⟨ q ⟩

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
≣-sym {.(Γ , _)} {.(Γ , _)} (Γ ⟪ p ⟫) = Γ ⟪ 2! p ⟫

≣-trans : {Γ Δ : Cx} {x y z : Γ ↦ Δ} → x ≣ y → y ≣ z → x ≣ z
≣-trans {.ε} {.ε} {Ξ} ∅∅ ∅∅ = ∅∅
≣-trans {.(Γ , _)} {.(Γ , _)} {Ξ} (Γ ⟪ p ⟫) (.Γ ⟪ q ⟫) = Γ ⟪ p ● q ⟫

≣-isEquiv : {Γ Δ : Cx} → IsEquivalence (_≣_ {Γ = Γ} {Δ = Δ})
≣-isEquiv = record { refl = ≣-refl ; sym = ≣-sym ; trans = ≣-trans }

∘↦-resp-≣ : {Γ Δ Ξ : Cx} {f h : Δ ↦ Ξ} {g i : Γ ↦ Δ}
           → f ≣ h → g ≣ i → f ∘↦ g ≣ h ∘↦ i
∘↦-resp-≣ ∅∅ ∅∅ = ∅∅
∘↦-resp-≣ (Γ ⟪ p ⟫) (.Γ ⟪ q ⟫) = Γ ⟪ q ⊡ p ⟫

open import Univ.Cats

ConCat : IsCategory Cx _↦_ _≣_
ConCat = record
          { id = id↦
          ; _∘_ = _∘↦_
          ; assoc = ∘↦-assoc
          ; identityˡ = ∘↦-idl
          ; identityʳ = ∘↦-idr
          ; equiv = ≣-isEquiv
          ; ∘-resp-≡ = ∘↦-resp-≣
          }
