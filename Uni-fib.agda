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

IsQinv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set _
IsQinv {ℓ} {ℓ'} {A} {B} f = Σ[ g ∈ (B → A) ] ((f ∘ g) ~ id) × ((g ∘ f) ~ id)

IsEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Set _
IsEquiv {A = A} {B = B} f = (Σ[ g ∈ (B → A) ] ((f ∘ g) ~ id) ) × (Σ[ h ∈ (B → A) ] ((h ∘ f) ~ id) )

IsEquiv→Qinv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} →
               IsEquiv f → IsQinv f
IsEquiv→Qinv {f = f} ((g , α) , (h , β)) =
             let γ : g ~ h
                 γ x = trans (sym (β (g x))) (cong h (α x))
             in  g , (α , (λ x → trans (γ (f x)) (β x)))

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

Σ≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {w w' : Σ[ x ∈ A ] P x}
   → (p : (proj₁ w ≡ proj₁ w')) → (subst P p) (proj₂ w) ≡ (proj₂ w') → w ≡ w'
Σ≡ refl refl = refl

ua : ∀ {ℓ} {A B : Set ℓ} → (A ≃ B) → (A ≡ B)
ua {ℓ} {A} {B} with IsEquiv→Qinv (univalence {A = A} {B = B})
ua {ℓ} {A} {B} | (f⁻¹ , α , β) = f⁻¹

pathConnected : ∀ {ℓ} (X : Set ℓ) → Set _
pathConnected X = (x y : X) → ∥ x ≡ y ∥

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

{--
Lemma : ∀ {ℓ} (F : Set ℓ) → Ω ⟪ F ⟫ {F , ∣ (ω refl) ∣} ≃ L.Lift (F ≃ F)
Lemma F = 𝒇 , (𝒇⁻¹ , α) , (𝒇⁻¹ , β)
  where
  𝒇 : Ω ⟪ F ⟫ → L.Lift (F ≃ F)
  𝒇 p = L.lift (ω (cong proj₁ p))

  𝒇⁻¹ : L.Lift (F ≃ F) → Ω ⟪ F ⟫
  𝒇⁻¹ (L.lift F≃F) = Σ≡ (ua F≃F) (trunIsProp _ _)

  proj₁≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
         → {a a' : A} {b : B a} {b' : B a'} {p : a ≡ a'} {q : subst B p b ≡ b'}
         → (cong proj₁ (Σ≡ p q)) ≡ p
  proj₁≡ {p = refl} {refl} = refl

  α : (𝒇 ∘ 𝒇⁻¹) ~ id
  α (L.lift F≃F) with (univalence {A = F} {B = F})
  ... | (g , α) , (h , β) = cong L.lift (trans (cong ω proj₁≡) (α F≃F))

  β : (𝒇⁻¹ ∘ 𝒇) ~ id
  β p = {!!}

α : ∀ {ℓ} {F : Set ℓ} → ⟪ F ⟫ → Set _
α = proj₁

Proposition : ∀ {ℓ} {F : Set ℓ} → IsUnivFib {A = ⟪ F ⟫} α
Proposition = {!!}

Theorem₁ : ∀ {ℓ} {A : Set ℓ} (B : A → Set ℓ) → pathConnected A
         → (F : Set ℓ) → Σ[ f ∈ (A → ⟪ F ⟫) ] (IsEquiv f × (α ∘ f) ~ B)
Theorem₁ = {!!}

Theorem₂ : ∀ {ℓ₁ ℓ₂} (X : Set ℓ₁) → pathConnected X → (F : Set ℓ₁) → L.Lift X ≃ ⟪ F ⟫
         → Σ[ P ∈ (X → Set ℓ₂) ] IsUnivFib P
Theorem₂ = {!!}
--}

------------------------------------------------------------------------------
-- What does ⟪ 𝟚 ⟫ look like?

-- There is a canonical element of ⟪ 𝟚 ⟫
-- and it is the only element up to ≡

`𝟚 : ⟪ 𝟚 ⟫
`𝟚 = 𝟚 , ∣ ω refl ∣

unique`𝟚 : (Xp : ⟪ 𝟚 ⟫) → ∥ Xp ≡ `𝟚 ∥
unique`𝟚 (X , ∣ X≃𝟚 ∣) = ∣ Σ≡  (ua X≃𝟚) (trunIsProp _ _)  ∣

-- 1-paths, i.e., elements of `𝟚 ≡ `𝟚; we have `id and `not and that's it

`id : `𝟚 ≡ `𝟚
`id = Σ≡ refl (trunIsProp _ _)

not≡ : 𝟚 ≡ 𝟚
not≡ = ua not≃
  where not² : (not ∘ not) ~ id
        not² false = refl
        not² true = refl
        not≃ : 𝟚 ≃ 𝟚
        not≃ = not , (not , not²) , (not , not²)

`not : `𝟚 ≡ `𝟚
`not = Σ≡ not≡ (trunIsProp _ _)

-- show every path is either id or not

-- 2-paths, i.e., elements of `id ≡ `id, `id ≡ `not, `not ≡ `id,
-- and `not ≡ `not

αid : `id ≡ `id
αid = refl

αnot : `not ≡ `not
αnot = refl

αidnot : `id ≡ `not
αidnot = {!!} -- empty but why

αnotid : `not ≡ `id
αnotid = {!!} -- empty but why

-- uniqueness of these paths

------------------------------------------------------------------------------
