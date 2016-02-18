module _ where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Universe
open import Rational

data τ : ℕ → Set where
  𝟘 : τ 0
  𝟙 : τ 1
  _⊕_ : ∀ {m n : ℕ} → τ m → τ n → τ (m + n)
  _⊗_ : ∀ {m n} → τ m → τ n → τ (m * n)

τ-univ : Indexed-universe _ _ _
τ-univ = record { I = ℕ ; U = τ ; El = ⟦_⟧ }
  where ⟦_⟧ : ∀ {n} → τ n → Set
        ⟦ 𝟘 ⟧ = ⊥
        ⟦ 𝟙 ⟧ = ⊤
        ⟦ t₁ ⊕ t₂ ⟧ = {!!}
        ⟦ t₁ ⊗ t₂ ⟧ = {!!}

data T : ℚ → Set where
  _/_ : ∀ {m n} → τ m → τ n → T (m / n)
  _⊞_ _⊠_ : ∀ {p q} → T p → T q → T (p ++ q)

T-univ : Indexed-universe _ _ _
T-univ = record { I = ℚ ; U = T ; El = ⟦_⟧ }
  where ⟦_⟧ : ∀ {q} → T q → Set
        ⟦ t₁ / t₂ ⟧ = {!!}
        ⟦ t₁ ⊞ t₂ ⟧ = {!!}
        ⟦ t₁ ⊠ t₂ ⟧ = {!!}

open import Function
open import Categories.Category
open import Relation.Binary.PropositionalEquality

τ-cat : ℕ → Category _ _ _
τ-cat n = record { Obj = τ n
                 ; _⇒_ = λ a b → El a → El b
                 ; _≡_ = _≡_
                 ; id = id
                 ; _∘_ = λ g f → g ∘ f
                 ; assoc = refl
                 ; identityˡ = refl
                 ; identityʳ = refl
                 ; equiv = isEquivalence
                 ; ∘-resp-≡ = ∘-resp-≡
                 }
      where open Indexed-universe τ-univ
            ∘-resp-≡ : {A B C : Set} {f h : B → C} {g i : A → B}
                     → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i
            ∘-resp-≡ refl refl = refl

T-cat : ℚ → Category _ _ _
T-cat q = record { Obj = T q
                 ; _⇒_ = λ a b → El a → El b
                 ; _≡_ = _≡_
                 ; id = id
                 ; _∘_ = λ g f → g ∘ f
                 ; assoc = refl
                 ; identityˡ = refl
                 ; identityʳ = refl
                 ; equiv = isEquivalence
                 ; ∘-resp-≡ = ∘-resp-≡
                 }
      where open Indexed-universe T-univ
            ∘-resp-≡ : {A B C : Set} {f h : B → C} {g i : A → B}
                     → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i
            ∘-resp-≡ refl refl = refl
open import Action

El : ∀ q → T q → Σ[ G ∈ Group _ _ ] Σ[ S ∈ Set _ ] Action G S
El (p / q) (T₁ / T₂) = {!!} , τ q , {!!}
El (._ / ._) (T₁ ⊞ T₂) = {!!}
El (._ / ._) (T₁ ⊠ T₂) = {!!}
