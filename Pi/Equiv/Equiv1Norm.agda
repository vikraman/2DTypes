{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.Equiv.Equiv1Norm where

open import Pi.Syntax.Pi+.Indexed as Pi
open import Pi.Syntax.Pi^ as Pi^

open import Pi.UFin.UFin
open import Pi.Common.Extra

open import Pi.Lehmer.Lehmer2 using (Lehmer)
open import Pi.Lehmer.Lehmer2FinEquiv
open import Pi.Coxeter.Lehmer2CoxeterEquiv
open import Pi.Coxeter.Sn
open import Pi.Coxeter.Coxeter
open import Pi.UFin.UFinLehmer2Equiv

open import Pi.Equiv.Equiv0Norm
open import Pi.Equiv.Equiv1NormHelpers

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.BAut
open import lib.types.Nat
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct
open import lib.types.Sigma


private
    variable
        n m : ℕ

lehmer2pi^ : {n m : ℕ} → (n == m) → Lehmer n → S n ⟷₁^ S m
lehmer2pi^ p cl = list2pi^I p (immersion cl)

pi^2lehmer : (S n) ⟷₁^ (S m) → Lehmer n
pi^2lehmer p = immersion⁻¹ (pi^2list p)

pi^2pi^ : (c : (S n) ⟷₁^ (S m)) →
    (lehmer2pi^ (ℕ-S-is-inj _ _ (⟷₁^-eq-size c)) (pi^2lehmer c)) ⟷₂^ c
pi^2pi^ {n} c with (⟷₁^-eq-size c)
... | idp =
    let lemma : immersion (immersion⁻¹ (pi^2list c)) ≈* (pi^2list c)
        lemma = immersion∘immersion⁻¹ (pi^2list c)
    in  _■^_ (piRespectsCoxI (ℕ-S-is-inj _ _ (⟷₁^-eq-size c)) _ _ lemma) (pi^2list2pi^ c)

lehmer2lehmer : {n : ℕ} → (p : Lehmer n) → pi^2lehmer (lehmer2pi^ idp p) == p
lehmer2lehmer {n} p =
    ap immersion⁻¹ (list2list (immersion p)) ∙ immersion⁻¹∘immersion p --

evalNorm₁ : (c : n ⟷₁^ m) → Aut (Fin n)
evalNorm₁ {O} c with (⟷₁^-eq-size c)
... | idp = ide _ -- zero case
evalNorm₁ {S n} c with (⟷₁^-eq-size c)
... | idp =
    let step1 : Lehmer n
        step1 = pi^2lehmer c

        step2 : Aut (Fin (S n))
        step2 = <– Fin≃Lehmer step1

    in  step2

fastevalNorm₁ : (c : S n ⟷₁^ S n) → Lehmer n
fastevalNorm₁ = pi^2lehmer


quoteNorm₁ : {n m : ℕ} → (pn : n == m) → Aut (Fin n) → n ⟷₁^ m
quoteNorm₁ {O} idp p = id⟷₁^
quoteNorm₁ {S n} {S m} q p =
    let step1 : Lehmer n
        step1 = –> Fin≃Lehmer p

        step2 = lehmer2pi^ (ℕ-S-is-inj _ _ q) step1
    in  step2

quote-evalNorm₁ : {n m : ℕ} → (c : n ⟷₁^ m) → quoteNorm₁ (⟷₁^-eq-size c) (evalNorm₁ c) ⟷₂^ c
quote-evalNorm₁ {O} c with (⟷₁^-eq-size c)
... | idp = (c₊⟷₂id⟷₁^ _) ■^ (!⟷₂^ (c₊⟷₂id⟷₁^ c))
quote-evalNorm₁ {S n} p with (⟷₁^-eq-size p)
... | idp =
    let cancelSn : –> Fin≃Lehmer (<– Fin≃Lehmer (pi^2lehmer p)) == pi^2lehmer p
        cancelSn = <–-inv-r Fin≃Lehmer (pi^2lehmer p)

        sizes = (ℕ-S-is-inj _ _ (⟷₁^-eq-size p))

        cancelNorm : lehmer2pi^ sizes (–> Fin≃Lehmer (<– Fin≃Lehmer (pi^2lehmer p))) ⟷₂^ p
        cancelNorm = transport (λ e -> lehmer2pi^ sizes e ⟷₂^ p) (! cancelSn) (pi^2pi^ p)

    in  cancelNorm

eval-quoteNorm₁ : {n : ℕ} → (p : Aut (Fin n)) → evalNorm₁ (quoteNorm₁ idp p) == p
eval-quoteNorm₁ {O} p = contr-has-all-paths {{Aut-FinO-level}} _ _
eval-quoteNorm₁ {S n} p =
    let cancelNorm : pi^2lehmer (lehmer2pi^ idp (–> Fin≃Lehmer p)) == (–> Fin≃Lehmer p)
        cancelNorm = lehmer2lehmer (–> Fin≃Lehmer p)

        cancelSn : <– Fin≃Lehmer (pi^2lehmer (lehmer2pi^ idp (–> Fin≃Lehmer p))) == p
        cancelSn = ap  (<– Fin≃Lehmer) cancelNorm ∙ <–-inv-l Fin≃Lehmer p

    in  cancelSn
