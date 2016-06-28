module 2D.Sing where

open import 2D.Types

open import Relation.Binary.PropositionalEquality

record Sing {τ : U} (p : τ ⟷ τ) : Set where
  constructor ⟪_,_⟫
  field
    p' : τ ⟷ τ
    eq : p' ⇔ p

_∘S_ : {τ : U} {p : τ ⟷ τ} → Sing p → Sing p → Sing p
⟪ p₁ , e₁ ⟫ ∘S ⟪ p₂ , e₂ ⟫ =
  ⟪ ! p₂ ◎ p₁ ◎ p₂ , assoc◎l ● (((⇔! e₂) ⊡ e₁) ⊡ id⇔) ● (rinv◎l ⊡ id⇔) ●
                     idl◎l ● e₂ ⟫
