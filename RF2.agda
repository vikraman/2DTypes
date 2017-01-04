{-# OPTIONS --without-K #-}

module RF2 where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Universe
open import Equiv
import TypeEquiv as T

infix 4 ⊢₀_ _≡₀_
infix 4 inl⟨_⟩≡ inr⟨_⟩≡
infix 5 ⟨_,_⟩
infix 6 ⟨_,_⟩≡
infix 50 _⊕_
infix 60 _⊗_
infix  30 _⟷_

data U₀ : Set where
  𝟘 𝟙 : U₀
  _⊕_ _⊗_ : U₀ → U₀ → U₀

data ⊢₀_ : U₀ → Set where
  ⋆ : ⊢₀ 𝟙
  inl : {A B : U₀} → (a : ⊢₀ A) → ⊢₀ (A ⊕ B)
  inr : {A B : U₀} → (b : ⊢₀ B) → ⊢₀ (A ⊕ B)
  ⟨_,_⟩ : {A B : U₀} → (a : ⊢₀ A) → (b : ⊢₀ B) → ⊢₀ (A ⊗ B)

data _≡₀_ : {A : U₀} (a b : ⊢₀ A) → Set where
  ⋆≡ : ⋆ ≡₀ ⋆
  inl⟨_⟩≡ : {A B : U₀} {a b : ⊢₀ A}
          → (p : a ≡₀ b) → inl {B = B} a ≡₀ inl b
  inr⟨_⟩≡ : {A B : U₀} {a b : ⊢₀ B}
          → (p : a ≡₀ b) → inr {A = A} a ≡₀ inr b
  ⟨_,_⟩≡ : {A B : U₀} {a b : ⊢₀ A} {c d : ⊢₀ B}
         → (p : a ≡₀ b) → (q : c ≡₀ d) → ⟨ a , c ⟩ ≡₀ ⟨ b , d ⟩

El₀ : U₀ → Set
El₀ 𝟘 = ⊥
El₀ 𝟙 = ⊤
El₀ (A ⊕ B) = El₀ A ⊎ El₀ B
El₀ (A ⊗ B) = El₀ A × El₀ B

El⊢₀ : {A : U₀} → ⊢₀ A → El₀ A
El⊢₀ ⋆ = tt
El⊢₀ (inl a) = inj₁ (El⊢₀ a)
El⊢₀ (inr b) = inj₂ (El⊢₀ b)
El⊢₀ ⟨ a , b ⟩ = El⊢₀ a , El⊢₀ b

El≡₀ : {A : U₀} {a b : ⊢₀ A} → a ≡₀ b → El⊢₀ a ≡ El⊢₀ b
El≡₀ ⋆≡ = refl
El≡₀ inl⟨ p ⟩≡ = cong inj₁ (El≡₀ p)
El≡₀ inr⟨ p ⟩≡ = cong inj₂ (El≡₀ p)
El≡₀ ⟨ p , q ⟩≡ = trans (cong (λ a → a , El⊢₀ _) (El≡₀ p))
                        (cong (λ b → El⊢₀ _ , b) (El≡₀ q))

TYPE₀ : Universe _ _
TYPE₀ = record { U = U₀; El = El₀ }

refl₀ : {A : U₀} → (a : ⊢₀ A) → a ≡₀ a
refl₀ ⋆ = ⋆≡
refl₀ (inl a) = inl⟨ refl₀ a ⟩≡
refl₀ (inr b) = inr⟨ refl₀ b ⟩≡
refl₀ ⟨ a , b ⟩ = ⟨ refl₀ a , refl₀ b ⟩≡

J₀ : {A : U₀}
   → {C : (a b : ⊢₀ A) → a ≡₀ b → Set}
   → (c : (a : ⊢₀ A) → C a a (refl₀ a))
   → (a b : ⊢₀ A) (p : a ≡₀ b)
   → C a b p
J₀ c .⋆ .⋆ ⋆≡ = c ⋆
J₀ c .(inl _) .(inl _) inl⟨ p ⟩≡ =
   J₀ (λ a → c (inl a)) _ _ p
J₀ c .(inr _) .(inr _) inr⟨ p ⟩≡ =
   J₀ (λ b → c (inr b)) _ _ p
J₀ c .(⟨ _ , _ ⟩) .(⟨ _ , _ ⟩) ⟨ p , q ⟩≡ =
   J₀ (λ a → J₀ (λ b → c ⟨ a , b ⟩) _ _ q) _ _ p

β₀ : {A : U₀}
   → {C : (a b : ⊢₀ A) → a ≡₀ b → Set}
   → {c : (a : ⊢₀ A) → C a a (refl₀ a)}
   → (a : ⊢₀ A)
   → J₀ {C = C} c a a (refl₀ a) ≡ c a
β₀ ⋆ = refl
β₀ (inl a) = β₀ a
β₀ (inr b) = β₀ b
β₀ ⟨ a , b ⟩ = trans (β₀ a) (β₀ b)

data _⟷_ : U₀ → U₀ → Set where
  unite₊l  : {t : U₀} → (𝟘 ⊕ t) ⟷ t
  uniti₊l  : {t : U₀} → t ⟷ (𝟘 ⊕ t)
  unite₊r  : {t : U₀} → (t ⊕ 𝟘) ⟷ t
  uniti₊r  : {t : U₀} → t ⟷ (t ⊕ 𝟘)
  swap₊    : {t₁ t₂ : U₀} → (t₁ ⊕ t₂) ⟷ (t₂ ⊕ t₁)
  assocl₊  : {t₁ t₂ t₃ : U₀} → (t₁ ⊕ (t₂ ⊕ t₃)) ⟷ ((t₁ ⊕ t₂) ⊕ t₃)
  assocr₊  : {t₁ t₂ t₃ : U₀} → ((t₁ ⊕ t₂) ⊕ t₃) ⟷ (t₁ ⊕ (t₂ ⊕ t₃))
  unite⋆l  : {t : U₀} → (𝟙 ⊗ t) ⟷ t
  uniti⋆l  : {t : U₀} → t ⟷ (𝟙 ⊗ t)
  unite⋆r  : {t : U₀} → (t ⊗ 𝟙) ⟷ t
  uniti⋆r  : {t : U₀} → t ⟷ (t ⊗ 𝟙)
  swap⋆    : {t₁ t₂ : U₀} → (t₁ ⊗ t₂) ⟷ (t₂ ⊗ t₁)
  assocl⋆  : {t₁ t₂ t₃ : U₀} → (t₁ ⊗ (t₂ ⊗ t₃)) ⟷ ((t₁ ⊗ t₂) ⊗ t₃)
  assocr⋆  : {t₁ t₂ t₃ : U₀} → ((t₁ ⊗ t₂) ⊗ t₃) ⟷ (t₁ ⊗ (t₂ ⊗ t₃))
  absorbr  : {t : U₀} → (𝟘 ⊗ t) ⟷ 𝟘
  absorbl  : {t : U₀} → (t ⊗ 𝟘) ⟷ 𝟘
  factorzr : {t : U₀} → 𝟘 ⟷ (t ⊗ 𝟘)
  factorzl : {t : U₀} → 𝟘 ⟷ (𝟘 ⊗ t)
  dist     : {t₁ t₂ t₃ : U₀} → ((t₁ ⊕ t₂) ⊗ t₃) ⟷ ((t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃))
  factor   : {t₁ t₂ t₃ : U₀} → ((t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃)) ⟷ ((t₁ ⊕ t₂) ⊗ t₃)
  distl    : {t₁ t₂ t₃ : U₀} → (t₁ ⊗ (t₂ ⊕ t₃)) ⟷ ((t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃))
  factorl  : {t₁ t₂ t₃ : U₀} → ((t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃)) ⟷ (t₁ ⊗ (t₂ ⊕ t₃))
  id⟷      : {t : U₀} → t ⟷ t
  _◎_      :  {t₁ t₂ t₃ : U₀} → (p : t₁ ⟷ t₂) → (q : t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_      :  {t₁ t₂ t₃ t₄ : U₀} → (p : t₁ ⟷ t₃) → (q : t₂ ⟷ t₄) → (t₁ ⊕ t₂ ⟷ t₃ ⊕ t₄)
  _⊗_      :  {t₁ t₂ t₃ t₄ : U₀} → (p : t₁ ⟷ t₃) → (q : t₂ ⟷ t₄) → (t₁ ⊗ t₂ ⟷ t₃ ⊗ t₄)

El⟷ : {A B : U₀} → A ⟷ B → El₀ A ≃ El₀ B
El⟷ unite₊l  = T.unite₊equiv
El⟷ uniti₊l  = T.uniti₊equiv
El⟷ unite₊r  = T.unite₊′equiv
El⟷ uniti₊r  = T.uniti₊′equiv
El⟷ swap₊    = T.swap₊equiv
El⟷ assocl₊  = T.assocl₊equiv
El⟷ assocr₊  = T.assocr₊equiv
El⟷ unite⋆l  = T.unite⋆equiv
El⟷ uniti⋆l  = T.uniti⋆equiv
El⟷ unite⋆r  = T.unite⋆′equiv
El⟷ uniti⋆r  = T.uniti⋆′equiv
El⟷ swap⋆    = T.swap⋆equiv
El⟷ assocl⋆  = T.assocl⋆equiv
El⟷ assocr⋆  = T.assocr⋆equiv
El⟷ absorbr  = T.distzequiv
El⟷ absorbl  = T.distzrequiv
El⟷ factorzr = T.factorzrequiv
El⟷ factorzl = T.factorzequiv
El⟷ dist     = T.distequiv
El⟷ factor   = T.factorequiv
El⟷ distl    = T.distlequiv
El⟷ factorl  = T.factorlequiv
El⟷ id⟷      = id≃
El⟷ (p ◎ q)  = El⟷ q ● El⟷ p
El⟷ (p ⊕ q)  = El⟷ p ⊎≃ El⟷ q
El⟷ (p ⊗ q)  = El⟷ p ×≃ El⟷ q

data U₁ : U₀ → Set where
  ⇑ : (A : U₀) → U₁ A

data _⊢₁_ : (A : U₀) → U₁ A → Set where
  ↑ : (A : U₀) → A ⊢₁ ⇑ A

_≡₁_ : {A : U₀} {A′ : U₁ A} (a b : A ⊢₁ A′) → Set
↑ A ≡₁ ↑ B = A ⟷ B

El₁ : {A : U₀} → U₁ A → Set
El₁ (⇑ A) = A ⊢₁ ⇑ A

El⊢₁ : {A : U₀} {A′ : U₁ A} → A ⊢₁ A′ → El₁ A′
El⊢₁ (↑ A) = ↑ A

postulate
  ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B

El≡₁ : {A : U₀} {A′ : U₁ A} {a b : A ⊢₁ A′} → a ≡₁ b → El⊢₁ a ≡ El⊢₁ b
El≡₁ {a = ↑ A} {↑ .A} p = cong (λ _ → ↑ A) (ua (El⟷ p))

TYPE₁ : Indexed-universe _ _ _
TYPE₁ = record { I = U₀ ; U = U₁ ; El = El₁ }

refl₁ : {A : U₀} {A′ : U₁ A} → (a : A ⊢₁ A′) → a ≡₁ a
refl₁ (↑ A) = id⟷

J₁ : {A : U₀} {A′ : U₁ A}
   → {C : (a b : A ⊢₁ A′) → a ≡₁ b → Set}
   → (c : (a : A ⊢₁ A′) → C a a (refl₁ a))
   → (a b : A ⊢₁ A′) (p : a ≡₁ b)
   → C a b p
J₁ c (↑ 𝟘) (↑ .𝟘) id⟷ = c (↑ 𝟘)
J₁ c (↑ 𝟘) (↑ .𝟘) (p ◎ q) = {!!}
J₁ c (↑ 𝟙) (↑ .𝟙) id⟷ = c (↑ 𝟙)
J₁ c (↑ 𝟙) (↑ .𝟙) (p ◎ q) = {!!}
J₁ c (↑ (A ⊕ B)) (↑ .(A ⊕ B)) p = {!!}
J₁ c (↑ (A ⊗ B)) (↑ .(A ⊗ B)) p = {!!}

β₁ : {A : U₀} {A′ : U₁ A}
   → {C : (a b : A ⊢₁ A′) → a ≡₁ b → Set}
   → {c : (a : A ⊢₁ A′) → C a a (refl₁ a)}
   → (a : A ⊢₁ A′)
   → J₁ {C = C} c a a (refl₁ a) ≡ c a
β₁ (↑ A) = {!!}
