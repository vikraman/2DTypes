{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Equiv where

open import lib.Base
open import lib.Equivalence
open import lib.types.Fin

open import Pi+.Coxeter.Lehmer
open import Pi+.Extra

Fin≃Lehmer : {n : ℕ} → (Fin n ≃ Fin n) ≃ Lehmer n
Fin≃Lehmer = TODO

open import Pi+.Coxeter.Group

Lehmer≃Coxeter : {n : ℕ} → Lehmer n ≃ Sn n
Lehmer≃Coxeter = TODO
