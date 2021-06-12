{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

module Pi+.Coxeter.LehmerSnEquiv where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.types.List

open import Pi+.Lehmer.Lehmer renaming (Lehmer to Lehmer1)
open import Pi+.Lehmer.Lehmer2
open import Pi+.Lehmer.LehmerLevel
open import Pi+.Coxeter.LehmerCoxeterEquiv
open import Pi+.Coxeter.Sn2

{-
Lehmer1≃Coxeter : {n : ℕ} ->  Lehmer1 n ≃ Sn (S n)
Lehmer1≃Coxeter = equiv f g f-g g-f
    where
    f : {n : ℕ} -> Lehmer1 n → Sn (S n)
    f {O} CanZ = q[ nil ]
    f {S n} = q[_] ∘ immersion

    g-q : {n : ℕ} ->  List (Fin n) → Lehmer1 n
    g-q = immersion⁻¹

    g-rel :  {n : ℕ} ->  {m1 m2 : List (Fin n)} → m1 ≈ m2 → g-q m1 == g-q m2
    g-rel = immersion⁻¹-respects≈

    g :  {n : ℕ} -> Sn (S n) → Lehmer1 n
    g {n} = SetQuot-rec {B = Lehmer1 n} g-q g-rel

    f-g-q : {n : ℕ} -> (m : List (Fin n)) → f (g q[ m ]) == q[ m ]
    f-g-q {O} nil = idp
    f-g-q {S n} m = quot-rel (immersion∘immersion⁻¹ m)

    f-g :  {n : ℕ} -> (l : Sn (S n)) → f (g l) == l
    f-g = SetQuot-elim {P = λ l → f (g l) == l} f-g-q (λ _ → prop-has-all-paths-↓)

    g-f : {n : ℕ} ->  (cl : Lehmer1 n) → g (f cl) == cl
    g-f {O} CanZ = idp
    g-f {S n} cl = immersion⁻¹∘immersion cl
 -}

Lehmer1≃Coxeter : {n : ℕ} -> Lehmer1 n ≃ Sn n
Lehmer1≃Coxeter = {!!}
