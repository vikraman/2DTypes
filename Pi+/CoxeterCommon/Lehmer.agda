{-# OPTIONS --without-K --rewriting #-}

module Pi+.CoxeterCommon.Lehmer where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.NType
open import lib.PathGroupoid

open import Pi+.CoxeterCommon.Arithmetic

data Lehmer : (n : ℕ) -> Type₀ where
  CanZ : Lehmer 0
  CanS : {n : ℕ} -> (l : Lehmer n) -> {r : ℕ} -> (r ≤ S n) -> Lehmer (S n)

open import Pi+.Extra

instance
  Lehmer-level : {n : ℕ} → is-set (Lehmer n)
  Lehmer-level = TODO