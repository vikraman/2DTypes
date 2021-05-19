{-# OPTIONS --without-K --rewriting #-}

module Pi+.Lehmer.Lehmer where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.NType
open import lib.PathGroupoid

open import Pi+.Common.Arithmetic

data Lehmer : (n : ℕ) -> Type₀ where
  CanZ : Lehmer 0
  CanS : {n : ℕ} -> (l : Lehmer n) -> {r : ℕ} -> (r ≤ S n) -> Lehmer (S n)

-- off-by-one
-- Lehmer 1 has two elements

x y : Lehmer 1
x = CanS CanZ z≤n -- r = 0
y = CanS CanZ (s≤s z≤n) -- r = 1
