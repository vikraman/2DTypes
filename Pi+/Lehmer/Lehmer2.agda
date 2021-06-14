{-# OPTIONS --without-K --rewriting #-}

module Pi+.Lehmer.Lehmer2 where

open import lib.Base
open import lib.types.Fin
open import lib.types.Sigma

Lehmer : ℕ → Type₀
Lehmer O = ⊤
Lehmer (S n) = Fin (S n) × Lehmer n
