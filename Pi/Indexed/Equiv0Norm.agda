{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.Indexed.Equiv0Norm where

open import Pi.Indexed.Syntax as Pi
open import Pi.Indexed.SyntaxHat as Pi^
open import Pi.UFin
open import Pi.Extra

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct
open import lib.types.Nat as N

private
  variable
    n m o p : ℕ

quoteNorm₀ : {n : ℕ} -> UFin[ n ] → ℕ
quoteNorm₀ {n} _ = n

evalNorm₀ : (n : ℕ) → UFin[ n ]
evalNorm₀ _ = pFin _

quote-evalNorm₀ : (n : ℕ) → quoteNorm₀ (evalNorm₀ n) ⟷₁^ n
quote-evalNorm₀ O = id⟷₁^
quote-evalNorm₀ (S n) = ⊕^ quote-evalNorm₀ n 

eval-quoteNorm₀ : {n : ℕ} (X : UFin[ n ]) → Trunc -1 (evalNorm₀ (quoteNorm₀ X) == X)
eval-quoteNorm₀ (X , ϕ) = Trunc-fmap (λ p → pair= p prop-has-all-paths-↓) ϕ