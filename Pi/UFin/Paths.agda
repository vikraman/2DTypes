{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.UFin.Paths where

open import HoTT
open import homotopy.FinSet
open import Pi.UFin.BAut
open import Pi.UFin.Univ

private
  variable
    i j k l : ULevel

loops : ℕ → Type₀
loops n = Aut (Fin n)

bpaths : ℕ → Type₀
bpaths n = Σ ℕ λ m → Fin m ≃ Fin n

Fin≃-inj : {n m : ℕ} → Fin n ≃ Fin m → n == m
Fin≃-inj e = Fin-inj _ _ (ua e)

module _ (n : ℕ) where

  l2b  : loops n → bpaths n
  l2b e = n , e

  b2l  : bpaths n → loops n
  b2l (m , e) = transport (λ k → Fin k ≃ Fin n) (Fin≃-inj e) e
