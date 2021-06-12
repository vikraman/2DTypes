{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

module Pi+.Coxeter.LehmerSnEquiv where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.types.List

open import Pi+.Lehmer.Lehmer2
open import Pi+.Lehmer.LehmerLevel
-- open import Pi+.Coxeter.LehmerCoxeterEquiv
open import Pi+.Coxeter.Sn

Lehmer≃Coxeter : {n : ℕ} ->  Lehmer n ≃ Sn n
Lehmer≃Coxeter = equiv f g f-g g-f
    where
    f : {n : ℕ} -> Lehmer n → Sn n
    f {O} CanZ = q[ nil ]
    f {S n} = q[_] ∘ immersion

    g-q : {n : ℕ} ->  List (Fin n) → Lehmer n
    g-q = immersion⁻¹

    g-rel :  {n : ℕ} ->  {m1 m2 : List (Fin n)} → m1 ≈ m2 → g-q m1 == g-q m2
    g-rel = immersion⁻¹-respects≈

    g :  {n : ℕ} -> Sn n → Lehmer n
    g {n} = SetQuot-rec {B = Lehmer n} g-q g-rel

    f-g-q : {n : ℕ} -> (m : List (Fin n)) → f (g q[ m ]) == q[ m ]
    f-g-q {O} nil = idp
    f-g-q {S n} m = quot-rel (immersion∘immersion⁻¹ m)

    f-g :  {n : ℕ} -> (l : Sn n) → f (g l) == l
    f-g = SetQuot-elim {P = λ l → f (g l) == l} f-g-q (λ _ → prop-has-all-paths-↓)

    g-f : {n : ℕ} ->  (cl : Lehmer n) → g (f cl) == cl
    g-f {O} CanZ = idp
    g-f {S n} cl = immersion⁻¹∘immersion cl
