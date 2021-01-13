{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Common.Lehmer where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.NType
open import lib.PathGroupoid

open import Pi+.Coxeter.Common.Arithmetic
open import Pi+.Coxeter.Common.ListN
open import Pi+.Coxeter.Common.LList
open import Pi+.Extra

data Lehmer : (n : ℕ) -> Type₀ where
  CanZ : Lehmer 0
  CanS : {n : ℕ} -> (l : Lehmer n) -> {r : ℕ} -> (r ≤ S n) -> Lehmer (S n)

immersion : {n : ℕ} -> Lehmer n -> Listℕ
immersion {0} CanZ = nil
immersion {S n} (CanS l {r} r≤1+n) = (immersion l) ++ (((S n) ∸ r) ↓ r)

immersion->> : {n : ℕ} -> (cl : Lehmer n) -> n >> immersion cl
immersion->> {.0} CanZ = nil
immersion->> {S n} (CanS {n} cl {r} rn) =
  let p = immersion->> {n} cl
  in  >>-++ (>>-S p) (>>-↓ (S n) (S n ∸ r) r (≤-reflexive (plus-minus rn)))

-- l0 : Lehmer 0
-- l0 = CanZ
-- l1 : Lehmer 1
-- l1 = CanS {0} CanZ {1} (s≤s z≤n)
-- l2 : Lehmer 2
-- l2 = CanS l1 {2} (s≤s (s≤s z≤n))

-- ll2 : Listℕ
-- ll2 = immersion {2} l2

instance
  Lehmer-level : {n : ℕ} → is-set (Lehmer n)
  Lehmer-level = TODO