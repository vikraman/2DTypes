{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

module Pi.Coxeter.NormEquiv where

open import HoTT

open import Pi.Coxeter.Sn
open import Pi.Coxeter.Coxeter
open import Pi.Coxeter.Lehmer2SnEquiv
open import Pi.Coxeter.Norm
open import Pi.Lehmer.Lehmer2
open import Pi.Common.Arithmetic
open import Pi.Common.InequalityEquiv

open import Pi.Common.Extra
open import Pi.Common.Misc

Lehmer≃im-norm : {n : ℕ} → Lehmer n ≃ im -1 (norm {n})
Lehmer≃im-norm = Sn≃im-norm ∘e Lehmer≃Coxeter
