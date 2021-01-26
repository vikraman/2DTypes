{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.UFin.Base where

open import HoTT
open import homotopy.FinSet public

open import Pi+.UFin.BAut

UFin = FinSet

instance
  FinSet-exp-level : is-gpd FinSet-exp
  FinSet-exp-level = Σ-level (raise-level 0 ℕ-level) λ n → BAut-level {{Fin-is-set}}

  FinSet-level : is-gpd FinSet
  FinSet-level = equiv-preserves-level FinSet-econv {{FinSet-exp-level}}
