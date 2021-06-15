{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Lehmer2CoxeterEquiv where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.types.List
open import lib.types.LoopSpace

open import Pi+.Lehmer.Lehmer2
open import Pi+.Lehmer.Lehmer renaming (Lehmer to Lehmer1)
open import Pi+.Coxeter.Sn
open import Pi+.Extra
open import Pi+.Misc
open import Pi+.UFin

immersion : {n : ℕ} -> Lehmer n -> List (Fin n)
immersion {n} c = TODO!

immersion⁻¹ : {n : ℕ} ->  List (Fin n) → Lehmer n
immersion⁻¹ {n} c = TODO!

immersion⁻¹-respects≈ :  {n : ℕ} ->  {m1 m2 : List (Fin n)} → m1 ≈ m2 → immersion⁻¹ m1 == immersion⁻¹ m2
immersion⁻¹-respects≈ {n} p = TODO!

immersion∘immersion⁻¹ : {n : ℕ} -> (m : List (Fin n)) → immersion (immersion⁻¹ m) ≈ m
immersion∘immersion⁻¹ {n} c = TODO!

immersion⁻¹∘immersion : {n : ℕ} ->  (cl : Lehmer n) → immersion⁻¹ (immersion cl) == cl
immersion⁻¹∘immersion {n} c = TODO!