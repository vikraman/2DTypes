{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.Experiments.Equiv.Equiv0 where

open import Pi.Syntax.Pi+.NonIndexed as Pi
open import Pi.UFin.UFin
open import Pi.Experiments.Equiv.Level0
open import Pi.Common.Extra

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