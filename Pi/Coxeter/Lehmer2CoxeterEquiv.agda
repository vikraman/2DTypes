{-# OPTIONS --without-K --rewriting #-}

module Pi.Coxeter.Lehmer2CoxeterEquiv where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.types.List
open import lib.types.LoopSpace

open import Pi.Lehmer.Lehmer2
open import Pi.Lehmer.Lehmer renaming (Lehmer to Lehmer1)
open import Pi.Coxeter.Sn
open import Pi.Coxeter.Coxeter
import Pi.Coxeter.LehmerCoxeterEquiv as L1
open import Pi.Extra
open import Pi.Misc
open import Pi.UFin.UFin

immersion : {n : ℕ} -> Lehmer n -> List (Fin n)
immersion {n} c = L1.immersion (<– Lehmer1-Lehmer2-equiv c)

immersion⁻¹ : {n : ℕ} ->  List (Fin n) → Lehmer n
immersion⁻¹ {n} c = –> Lehmer1-Lehmer2-equiv (L1.immersion⁻¹ c)

immersion⁻¹-respects≈ :  {n : ℕ} ->  {m1 m2 : List (Fin n)} → m1 ≈* m2 → immersion⁻¹ m1 == immersion⁻¹ m2
immersion⁻¹-respects≈ {n} p = ap (–> Lehmer1-Lehmer2-equiv) (L1.immersion⁻¹-respects≈ p)

immersion∘immersion⁻¹ : {n : ℕ} -> (m : List (Fin n)) → immersion (immersion⁻¹ m) ≈* m
immersion∘immersion⁻¹ {n} c =
    let r = L1.immersion∘immersion⁻¹ c
        t = ap L1.immersion (<–-inv-l Lehmer1-Lehmer2-equiv (L1.immersion⁻¹ c))
    in  (idp≃ _ _ t) ■ r

immersion⁻¹∘immersion : {n : ℕ} ->  (cl : Lehmer n) → immersion⁻¹ (immersion cl) == cl
immersion⁻¹∘immersion {n} c =
    let r = ap (–> Lehmer1-Lehmer2-equiv) $ L1.immersion⁻¹∘immersion (<– Lehmer1-Lehmer2-equiv c)
        t = <–-inv-r Lehmer1-Lehmer2-equiv c
    in  r ∙ t
