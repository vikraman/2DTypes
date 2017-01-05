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

infix 4 ⊢₀_ _=₀_ _≡₀_
infix 4 inl⟨_⟩= inr⟨_⟩=
infix 5 ⟨_,_⟩
infix 6 ⟨_,_⟩=
infix 50 _⊕_
infix 60 _⊗_
-- types
data U₀ : Set where
  𝟘 𝟙 : U₀
  _⊕_ _⊗_ : U₀ → U₀ → U₀

El₀ : U₀ → Set
El₀ 𝟘 = ⊥
El₀ 𝟙 = ⊤
El₀ (A ⊕ B) = El₀ A ⊎ El₀ B
El₀ (A ⊗ B) = El₀ A × El₀ B

-- terms
data ⊢₀_ : U₀ → Set where
  ⋆ : ⊢₀ 𝟙
  inl : {A B : U₀} → (a : ⊢₀ A) → ⊢₀ (A ⊕ B)
  inr : {A B : U₀} → (b : ⊢₀ B) → ⊢₀ (A ⊕ B)
  ⟨_,_⟩ : {A B : U₀} → (a : ⊢₀ A) → (b : ⊢₀ B) → ⊢₀ (A ⊗ B)

El⊢₀ : {A : U₀} → ⊢₀ A → El₀ A
El⊢₀ ⋆ = tt
El⊢₀ (inl a) = inj₁ (El⊢₀ a)
El⊢₀ (inr b) = inj₂ (El⊢₀ b)
El⊢₀ ⟨ a , b ⟩ = El⊢₀ a , El⊢₀ b

-- judgmental equality on terms
data _=₀_ : {A : U₀} (a b : ⊢₀ A) → Set where
  ⋆=      : ⋆ =₀ ⋆
  inl⟨_⟩= : {A B : U₀} {a b : ⊢₀ A}
          → (p : a =₀ b) → inl {B = B} a =₀ inl b
  inr⟨_⟩= : {A B : U₀} {a b : ⊢₀ B}
          → (p : a =₀ b) → inr {A = A} a =₀ inr b
  ⟨_,_⟩=  : {A B : U₀} {a b : ⊢₀ A} {c d : ⊢₀ B}
          → (p : a =₀ b) → (q : c =₀ d) → ⟨ a , c ⟩ =₀ ⟨ b , d ⟩

El=₀ : {A : U₀} {a b : ⊢₀ A} → a =₀ b → El⊢₀ a ≡ El⊢₀ b
El=₀ ⋆= = refl
El=₀ inl⟨ p ⟩= = cong inj₁ (El=₀ p)
El=₀ inr⟨ p ⟩= = cong inj₂ (El=₀ p)
El=₀ ⟨ p , q ⟩= = trans (cong (λ a → a , El⊢₀ _) (El=₀ p))
                        (cong (λ b → El⊢₀ _ , b) (El=₀ q))

TYPE₀ : Universe _ _
TYPE₀ = record { U = U₀; El = El₀ }

-- refl
refl=₀ : {A : U₀} → (a : ⊢₀ A) → a =₀ a
refl=₀ ⋆ = ⋆=
refl=₀ (inl a) = inl⟨ refl=₀ a ⟩=
refl=₀ (inr b) = inr⟨ refl=₀ b ⟩=
refl=₀ ⟨ a , b ⟩ = ⟨ refl=₀ a , refl=₀ b ⟩=

-- path induction
J=₀ : {A : U₀}
    → {C : (a b : ⊢₀ A) → a =₀ b → Set}
    → (c : (a : ⊢₀ A) → C a a (refl=₀ a))
    → {a b : ⊢₀ A} (p : a =₀ b)
    → C a b p
J=₀ c ⋆= = c ⋆
J=₀ c inl⟨ p ⟩= = J=₀ (λ a → c (inl a)) p
J=₀ c inr⟨ p ⟩= = J=₀ (λ b → c (inr b)) p
J=₀ c ⟨ p , q ⟩= = J=₀ (λ a → J=₀ (λ b → c ⟨ a , b ⟩) q) p

-- path induction computes
Jβ=₀ : {A : U₀}
    → {C : (a b : ⊢₀ A) → a =₀ b → Set}
    → {c : (a : ⊢₀ A) → C a a (refl=₀ a)}
    → (a : ⊢₀ A)
    → J=₀ {C = C} c (refl=₀ a) ≡ c a
Jβ=₀ ⋆ = refl
Jβ=₀ (inl a) = Jβ=₀ a
Jβ=₀ (inr b) = Jβ=₀ b
Jβ=₀ ⟨ a , b ⟩ = trans (Jβ=₀ a) (Jβ=₀ b)

-- identity types
data _≡₀_ : U₀ → U₀ → Set where
  unite₊l  : {A : U₀} → (𝟘 ⊕ A) ≡₀ A
  uniti₊l  : {A : U₀} → A ≡₀ (𝟘 ⊕ A)
  unite₊r  : {A : U₀} → (A ⊕ 𝟘) ≡₀ A
  uniti₊r  : {A : U₀} → A ≡₀ (A ⊕ 𝟘)
  swap₊    : {A B : U₀} → (A ⊕ B) ≡₀ (B ⊕ A)
  assocl₊  : {A B C : U₀} → (A ⊕ (B ⊕ C)) ≡₀ ((A ⊕ B) ⊕ C)
  assocr₊  : {A B C : U₀} → ((A ⊕ B) ⊕ C) ≡₀ (A ⊕ (B ⊕ C))
  unite⋆l  : {A : U₀} → (𝟙 ⊗ A) ≡₀ A
  uniti⋆l  : {A : U₀} → A ≡₀ (𝟙 ⊗ A)
  unite⋆r  : {A : U₀} → (A ⊗ 𝟙) ≡₀ A
  uniti⋆r  : {A : U₀} → A ≡₀ (A ⊗ 𝟙)
  swap⋆    : {A B : U₀} → (A ⊗ B) ≡₀ (B ⊗ A)
  assocl⋆  : {A B C : U₀} → (A ⊗ (B ⊗ C)) ≡₀ ((A ⊗ B) ⊗ C)
  assocr⋆  : {A B C : U₀} → ((A ⊗ B) ⊗ C) ≡₀ (A ⊗ (B ⊗ C))
  absorbr  : {A : U₀} → (𝟘 ⊗ A) ≡₀ 𝟘
  absorbl  : {A : U₀} → (A ⊗ 𝟘) ≡₀ 𝟘
  factorzr : {A : U₀} → 𝟘 ≡₀ (A ⊗ 𝟘)
  factorzl : {A : U₀} → 𝟘 ≡₀ (𝟘 ⊗ A)
  dist     : {A B C : U₀} → ((A ⊕ B) ⊗ C) ≡₀ ((A ⊗ C) ⊕ (B ⊗ C))
  factor   : {A B C : U₀} → ((A ⊗ C) ⊕ (B ⊗ C)) ≡₀ ((A ⊕ B) ⊗ C)
  distl    : {A B C : U₀} → (A ⊗ (B ⊕ C)) ≡₀ ((A ⊗ B) ⊕ (A ⊗ C))
  factorl  : {A B C : U₀} → ((A ⊗ B) ⊕ (A ⊗ C)) ≡₀ (A ⊗ (B ⊕ C))
  id≡₀     : {A : U₀} → A ≡₀ A
  _◎_      :  {A B C : U₀} → (p : A ≡₀ B) → (q : B ≡₀ C) → (A ≡₀ C)
  _⊕_      :  {A B C D : U₀} → (p : A ≡₀ C) → (q : B ≡₀ D) → (A ⊕ B ≡₀ C ⊕ D)
  _⊗_      :  {A B C D : U₀} → (p : A ≡₀ C) → (q : B ≡₀ D) → (A ⊗ B ≡₀ C ⊗ D)

-- (p : A ≡ B) → transport (λ x → x) p
eval₀ : {A B : U₀} → (p : A ≡₀ B) → ⊢₀ A → ⊢₀ B
eval₀ p v = {!!}

-- use eval₀ to define El-eval₀
El-eval₀ : {A B : U₀} → (p : A ≡₀ B) → El₀ A → El₀ B
El-eval₀ {𝟘} p ()
El-eval₀ {𝟙} p tt = El⊢₀ (eval₀ p ⋆)
El-eval₀ {A ⊕ B} p (inj₁ a) = {!!}
El-eval₀ {A ⊕ B} p (inj₂ b) = {!!}
El-eval₀ {A ⊗ B} p (a , b) = {!!}

-- decode to equivalence
El≡₀ : {A B : U₀} → A ≡₀ B → El₀ A ≃ El₀ B
El≡₀ unite₊l  = T.unite₊equiv
El≡₀ uniti₊l  = T.uniti₊equiv
El≡₀ unite₊r  = T.unite₊′equiv
El≡₀ uniti₊r  = T.uniti₊′equiv
El≡₀ swap₊    = T.swap₊equiv
El≡₀ assocl₊  = T.assocl₊equiv
El≡₀ assocr₊  = T.assocr₊equiv
El≡₀ unite⋆l  = T.unite⋆equiv
El≡₀ uniti⋆l  = T.uniti⋆equiv
El≡₀ unite⋆r  = T.unite⋆′equiv
El≡₀ uniti⋆r  = T.uniti⋆′equiv
El≡₀ swap⋆    = T.swap⋆equiv
El≡₀ assocl⋆  = T.assocl⋆equiv
El≡₀ assocr⋆  = T.assocr⋆equiv
El≡₀ absorbr  = T.distzequiv
El≡₀ absorbl  = T.distzrequiv
El≡₀ factorzr = T.factorzrequiv
El≡₀ factorzl = T.factorzequiv
El≡₀ dist     = T.distequiv
El≡₀ factor   = T.factorequiv
El≡₀ distl    = T.distlequiv
El≡₀ factorl  = T.factorlequiv
El≡₀ id≡₀     = id≃
El≡₀ (p ◎ q)  = El≡₀ q ● El≡₀ p
El≡₀ (p ⊕ q)  = El≡₀ p ⊎≃ El≡₀ q
El≡₀ (p ⊗ q)  = El≡₀ p ×≃ El≡₀ q

-- should compute and match up with the transported term
Elβ₁≡₀ : {A B : U₀} → (p : A ≡₀ B) → (a : ⊢₀ A) (b : ⊢₀ B) → _≃_.f (El≡₀ p) ≡ El-eval₀ p
Elβ₁≡₀ p = {!!}

-- lift everything to level 1
data U₁ : U₀ → Set where
  ⇑ : (A : U₀) → U₁ A

data _⊢₁_ : (A : U₀) → U₁ A → Set where
  ↑ : (A : U₀) → A ⊢₁ ⇑ A

_≡₁_ : {A : U₀} {A′ : U₁ A} (a b : A ⊢₁ A′) → Set
↑ A ≡₁ ↑ B = A ≡₀ B

-- not sure about these yet
El₁ : {A : U₀} → U₁ A → Set
El₁ (⇑ A) = A ⊢₁ ⇑ A

El⊢₁ : {A : U₀} {A′ : U₁ A} → A ⊢₁ A′ → El₁ A′
El⊢₁ (↑ A) = ↑ A

postulate
  ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B

El≡₁ : {A : U₀} {A′ : U₁ A} {a b : A ⊢₁ A′} → a ≡₁ b → El⊢₁ a ≡ El⊢₁ b
El≡₁ {a = ↑ A} {↑ .A} p = cong (λ _ → ↑ A) (ua (El≡₀ p))

TYPE₁ : Indexed-universe _ _ _
TYPE₁ = record { I = U₀ ; U = U₁ ; El = El₁ }
