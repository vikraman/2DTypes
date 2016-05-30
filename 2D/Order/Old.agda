module 2D.Order.Old where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import 2D.Types
open import 2D.Pi

open import Relation.Binary.PropositionalEquality

data apⁿ {τ : U} (p : τ ⟷ τ) : ℕ → Set where
  ap¹ : apⁿ p 1
  apˢ : ∀ {n} → apⁿ p n → apⁿ p (suc n)

module _ {τ : U} {p : τ ⟷ τ} where
  ⟦_⟧apⁿ : {n : ℕ} → apⁿ p n → ⟦ τ ⟧ → ⟦ τ ⟧
  ⟦ ap¹ ⟧apⁿ v = ap p v
  ⟦ apˢ a ⟧apⁿ v = ap p (⟦ a ⟧apⁿ v)

open import Data.Nat.LCM using (lcm)

lcm' : ℕ → ℕ → ℕ
lcm' i j with lcm i j
... | k , _ = k

order : (τ : U) (p : τ ⟷ τ)
      → Σ[ n ∈ ℕ ] Σ[ a ∈ apⁿ p n ] (∀ v → ⟦ a ⟧apⁿ v ≡ v)
order ZERO id⟷ = 1 , ap¹ , λ ()
order ZERO (p₁ ◎ p₂) = 1 , ap¹ , λ ()
order ONE id⟷ = 1 , ap¹ , λ { tt → refl }
order ONE (p₁ ◎ p₂) = 1 , ap¹ , λ { tt → refl }
order (PLUS τ .τ) swap₊ = 2 , apˢ ap¹ , λ { (inj₁ x) → refl ; (inj₂ y) → refl }
order (PLUS τ₁ τ₂) id⟷ = 1 , ap¹ , λ v → refl
order (PLUS τ₁ τ₂) (p₁ ◎ p₂) = {!!}
order (PLUS τ₁ τ₂) (p₁ ⊕ p₂) with (order τ₁ p₁ , order τ₂ p₂)
... | (n₁ , a₁ , pf₁) , (n₂ , a₂ , pf₂) = lcm' n₁ n₂ , {!!} , λ { (inj₁ x) → {!!} ; (inj₂ y) → {!!} }
order (TIMES τ .τ) swap⋆ = 2 , apˢ ap¹ , λ { (proj₁ , proj₂) → refl }
order (TIMES τ₁ τ₂) id⟷ = 1 , ap¹ , λ v → refl
order (TIMES τ₁ τ₂) (p₁ ◎ p₂) = {!!}
order (TIMES τ₁ τ₂) (p₁ ⊗ p₂) with (order τ₁ p₁ , order τ₂ p₂)
... | (n₁ , a₁ , pf₁) , (n₂ , a₂ , pf₂) = lcm' n₁ n₂ , {!!} , λ { (proj₁ , proj₂) → {!!} }
