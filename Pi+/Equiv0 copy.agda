{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Conjectures where

open import Pi+.Syntax as Pi
open import Pi+.UFin
open import Pi+.Level0
open import Pi+.Extra

open import Pi+.Coxeter.Common.Lehmer
open import Pi+.Coxeter.Parametrized.Equiv


open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct

∣⟪_⟫∣ : (n : ℕ) → ∣ ⟪ n ⟫ ∣ == n 
∣⟪ O ⟫∣ = idp
∣⟪ S n ⟫∣ = ap S ∣⟪ n ⟫∣

eval₀ : U → UFin
eval₀ X = FinFS ∣ X ∣

quote₀ : UFin → U
quote₀ X = ⟪ card X ⟫

quote-eval₀ : (X : U) → quote₀ (eval₀ X) ⟷₁ X
quote-eval₀ O = id⟷₁
quote-eval₀ I = swap₊ ◎ unite₊l
quote-eval₀ (X + Y) = !⟷₁ (normC (X + Y))

eval-quote₀ : (X : UFin) → Trunc -1 (eval₀ (quote₀ X) == X)
eval-quote₀ = FinSet-elim-prop (λ _ → Trunc-level) λ n → [ pair= (ap Fin ∣⟪ n ⟫∣) prop-has-all-paths-↓ ]

postulate
    pi2normpi : {X Y : U} → X ⟷₁ Y → ⟪ ∣ X ∣ ⟫ ⟷₁ ⟪ ∣ Y ∣ ⟫

eval₁ : {X Y : U} → X ⟷₁ Y → eval₀ X == eval₀ Y
eval₁ {X} {Y} p = ?

quote₁ : {X Y : UFin} → X == Y → quote₀ X ⟷₁ quote₀ Y
quote₁ = TODO

quote-eval₁ : {X Y : U} → (p : X ⟷₁ Y) → quote₁ (eval₁ p) ⟷₂ (quote-eval₀ X ◎ p ◎ !⟷₁ (quote-eval₀ Y))
quote-eval₁ p = TODO

eval-quote₁ : {X Y : UFin} → (p : X == Y) → eval₁ (quote₁ p) == ap (λ X → eval₀ (quote₀ X)) p
eval-quote₁ p = TODO

eval₂ : {X Y : U} {p q : X ⟷₁ Y } → p ⟷₂ q → eval₁ p == eval₁ q
eval₂ {p = p} {q = q} α = TODO

quote₂ : {X Y : UFin} {p q : X == Y} (α : p == q) → quote₁ p ⟷₂ quote₁ q
quote₂ {p = p} {q = q} α = transport (λ e → quote₁ p ⟷₂ quote₁ e) α id⟷₂

quote-eval₂ : {X Y : U} {p q : X ⟷₁ Y } (α : p ⟷₂ q) → quote₂ (eval₂ α) ⟷₃
    trans⟷₂ (quote-eval₁ p) (trans⟷₂ (id⟷₂ ⊡ (α ⊡ id⟷₂)) (!⟷₂ (quote-eval₁ q)))
quote-eval₂ {p = p} {q = q} α = trunc (quote₂ (eval₂ α)) (trans⟷₂ (quote-eval₁ p) (trans⟷₂ (id⟷₂ ⊡ (α ⊡ id⟷₂)) (!⟷₂ (quote-eval₁ q))))

eval-quote₂ : {X Y : UFin} {p q : X == Y} (α : p == q) → eval₂ (quote₂ α) == ap (λ e → eval₁ (quote₁ e)) α
eval-quote₂ α = prop-has-all-paths {{has-level-apply (has-level-apply UFin-is-gpd _ _) _ _}} _ _
