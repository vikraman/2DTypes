{-# OPTIONS --without-K #-}

module Uni-fib where

import Level as L
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality

_~_ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f g : A → B) → Set _
_~_ {A = A} f g = (a : A) → f a ≡ g a

IsEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Set _
IsEquiv {A = A} {B = B} f = (Σ[ g ∈ (B → A) ] ((f ∘ g) ~ id) ) × (Σ[ h ∈ (B → A) ] ((h ∘ f) ~ id) )

_≃_ : ∀ {ℓ} (A B : Set ℓ) → Set _
A ≃ B = Σ[ f ∈ (A → B) ] (IsEquiv f)

ω : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
ω refl = id , (id , (λ _ → refl)) , (id , (λ _ → refl))

ap : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) → {a a' : A} → a ≡ a' → (B a ≡ B a')
ap B refl = refl

IsUnivFib : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂)  → Set _
IsUnivFib {A = A} B = {a a' : A} → IsEquiv {A = (a ≡ a')} {B = (B a ≃ B a')} (ω ∘ ap B)

isProp : ∀ {ℓ} (P : Set ℓ) → Set _
isProp P = (x y : P) → x ≡ y

data ∥_∥ {ℓ} (A : Set ℓ) : Set ℓ where
  ∣_∣ : A → ∥ A ∥
postulate
  trunIsProp : ∀ {ℓ} {A : Set ℓ} → isProp ∥ A ∥
  univalence : ∀ {ℓ} {A B : Set ℓ} → IsEquiv (ω {A = A} {B = B})
  funext : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x}
         → ((x : A) → f x ≡ g x) → f ≡ g

ua : ∀ {ℓ} {A B : Set ℓ} → (A ≃ B) → (A ≡ B)
ua {ℓ} {A} {B} with univalence {A = A} {B = B}
ua {ℓ} {A} {B} | (g , α) , (h , β) = h

⟪_⟫ : ∀ {ℓ} (F : Set ℓ) → Set _
⟪_⟫ F = Σ[ Y ∈ (Set _) ] (∥ Y ≃ F ∥)

UA : ∀ {ℓ} {A : Set ℓ} → Set _
UA {ℓ} {A} = IsUnivFib {ℓ₁ = L.suc ℓ} id


𝟚 𝟙 𝟘 : Set
𝟚 = Bool
𝟙 = ⊤
𝟘 = ⊥

uniq𝟙 : (x : 𝟙) →  x ≡ tt
uniq𝟙 tt = refl

uniq[tt≡tt] : {p : tt ≡ tt} → p ≡ refl
uniq[tt≡tt] {refl} = refl

uniq𝟙≃𝟙 : (eq : 𝟙 ≃ 𝟙) → eq ≡ ω refl
uniq𝟙≃𝟙 (f , (g , α) , (h , β))
  rewrite funext {f = f} {g = id} uniq𝟙
        | funext {f = g} {g = id} uniq𝟙
        | funext {f = h} {g = id} uniq𝟙
        | funext {f = α} {g = λ _ → refl} (λ {tt → uniq[tt≡tt]})
        | funext {f = β} {g = λ _ → refl} (λ {tt → uniq[tt≡tt]}) = refl

uniq𝟘≃𝟘 : (eq : 𝟘 ≃ 𝟘) → eq ≡ ω refl
uniq𝟘≃𝟘 (f , (g , α) , (h , β))
  with funext {f = f} {g = id} (λ ())
     | funext {f = g} {g = id} (λ ())
     | funext {f = h} {g = id} (λ ())
...  | refl | refl | refl = trans (cong (λ x → (id , (id , x) , id , β)) α≡)
                                  (cong (λ x → (id , (id , (λ _ → refl)) , id , x)) β≡)
  where
  α≡ : α ≡ (λ _ → refl)
  α≡ = funext (λ ())
  β≡ : β ≡ (λ _ → refl)
  β≡ = funext (λ ())

module ex1 where
  P : 𝟙 → Set
  P = λ _ → 𝟙

  PIsUnivFib : IsUnivFib P
  PIsUnivFib = ((λ _ → refl) , (λ {a → sym (uniq𝟙≃𝟙 a)}))
             , ((λ x → refl) , (λ {refl → refl}))

module ex2 where
  P : 𝟙 → Set
  P = λ _ → 𝟘

  PIsUnivFib : IsUnivFib P
  PIsUnivFib = ((λ _ → refl) , (λ {a → sym (uniq𝟘≃𝟘 a)}))
             , ((λ x → refl) , (λ {refl → refl}))

module ex3 where
  P : 𝟚 → Set
  P false = 𝟘
  P true = 𝟙

  f⁻¹ : {b b' : 𝟚} → P b ≃ P b' → b ≡ b'
  f⁻¹ {false} {false} _ = refl
  f⁻¹ {false} {true} (f , (g , α) , (h , β)) = ⊥-elim (g tt)
  f⁻¹ {true} {false} (f , (g , α) , (h , β)) = ⊥-elim (f tt)
  f⁻¹ {true} {true} _ = refl

  α : {b b' : 𝟚} → (eq : P b ≃ P b') → ω (ap P (f⁻¹ eq)) ≡ eq
  α {false} {false} eq = sym (uniq𝟘≃𝟘 eq)
  α {false} {true} (f , (g , α) , (h , β)) = ⊥-elim (g tt)
  α {true} {false} (f , (g , α) , (h , β)) = ⊥-elim (f tt)
  α {true} {true} eq = sym (uniq𝟙≃𝟙 eq)

  β : {b b' : 𝟚} → (eq : b ≡ b') → f⁻¹ (ω (ap P eq)) ≡ eq
  β {false} {false} refl = refl
  β {false} {true} ()
  β {true} {false} ()
  β {true} {true} refl = refl

  PIsUnivFib : IsUnivFib P
  PIsUnivFib = (f⁻¹ , α) , (f⁻¹ , β)

Ω : ∀ {ℓ} (A : Set ℓ) {a : A} → Set _
Ω A {a} = a ≡ a

Lemma : ∀ {ℓ} (F : Set ℓ) → Ω ⟪ F ⟫ {F , ∣ (ω refl) ∣} ≃ L.Lift (F ≃ F)
Lemma F = 𝒇 , (𝒇⁻¹ , {!!}) , (𝒇⁻¹ , {!!})
  where
  𝒇 : Ω ⟪ F ⟫ → L.Lift (F ≃ F)
  𝒇 p = L.lift {!!}

  𝒇⁻¹ : L.Lift (F ≃ F) → Ω ⟪ F ⟫
  𝒇⁻¹ (L.lift (f , (g , α) , (h , β))) = {!!}
