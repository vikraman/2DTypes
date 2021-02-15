{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Indexed.Equiv0 where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.UFin
open import Pi+.Extra

open import Pi+.Indexed.Equiv0Hat
open import Pi+.Indexed.Equiv0Norm
open import Pi+.Indexed.Equiv1Hat

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

quote₀ : UFin[ n ] → U n
quote₀ = quote^₀ ∘ quoteNorm₀

eval₀ : U n → UFin[ n ]
eval₀ = evalNorm₀ ∘ eval^₀

quote-eval₀ : (t : U n) → quote₀ (eval₀ t) ⟷₁ t
quote-eval₀ t = quote^₁ (quote-evalNorm₀ (eval^₀ t)) ◎ quote-eval^₀ t

eval-quote₀ : {n : ℕ} (X : UFin[ n ]) → Trunc -1 (eval₀ (quote₀ X) == X)
eval-quote₀ = eval-quoteNorm₀