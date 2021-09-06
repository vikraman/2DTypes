{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.Equiv.Equiv0 where

open import Pi.Syntax.Pi+.Indexed as Pi
open import Pi.Syntax.Pi^ as Pi^
open import Pi.UFin
open import Pi.Extra

open import Pi.Equiv.Equiv0Hat
open import Pi.Equiv.Equiv0Norm
open import Pi.Equiv.Equiv1Hat

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
