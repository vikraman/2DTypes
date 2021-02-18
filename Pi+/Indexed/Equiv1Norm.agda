{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.Indexed.Equiv1Norm where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^

open import Pi+.UFin
open import Pi+.Extra

open import Pi+.Lehmer.Lehmer using (Lehmer)
open import Pi+.Lehmer.LehmerFinEquiv
open import Pi+.Coxeter.LehmerCoxeterEquiv
open import Pi+.Coxeter.Sn
open import Pi+.UFinLehmerEquiv

open import Pi+.Indexed.Equiv0Norm
open import Pi+.Indexed.Equiv1NormHelpers

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

lehmer2normpi : {n m : ℕ} → (n == m) → Lehmer n → S n ⟷₁^ S m
lehmer2normpi p cl = list2normI p (immersion cl)

normpi2lehmer : (S n) ⟷₁^ (S m) → Lehmer n
normpi2lehmer p = immersion⁻¹ (norm2list p)

normpi2normpi : (c : (S n) ⟷₁^ (S m)) →
    (lehmer2normpi (ℕ-S-is-inj _ _ (⟷₁^-eq-size c)) (normpi2lehmer c)) ⟷₂^ c
normpi2normpi {n} c =
    let lemma : immersion (immersion⁻¹ (norm2list c)) ≈ (norm2list c)
        lemma = immersion∘immersion⁻¹ (norm2list c)
    in  trans⟷₂^ (piRespectsCoxI (ℕ-S-is-inj _ _ (⟷₁^-eq-size c)) _ _ lemma) (norm2norm c)

lehmer2lehmer : {n : ℕ} → (p : Lehmer n) → normpi2lehmer (lehmer2normpi idp p) == p
lehmer2lehmer {n} p = 
    ap immersion⁻¹ (list2list (immersion p)) ∙ immersion⁻¹∘immersion p -- 

evalNorm₁ : (c : n ⟷₁^ m) → Aut (Fin n)
evalNorm₁ {O} c with (⟷₁^-eq-size c)
... | idp = ide _ -- zero case
evalNorm₁ {S n} c with (⟷₁^-eq-size c)
... | idp =
    let step1 : Lehmer n
        step1 = normpi2lehmer c

        step2 : Aut (Fin (S n))
        step2 = <– Fin≃Lehmer step1

    in  step2

quoteNorm₁ : {n m : ℕ} → (pn : n == m) → Aut (Fin n) → n ⟷₁^ m
quoteNorm₁ {O} idp p = id⟷₁^
quoteNorm₁ {S n} {S m} q p =
    let step1 : Lehmer n
        step1 = –> Fin≃Lehmer p

        step2 = lehmer2normpi (ℕ-S-is-inj _ _ q) step1
    in  step2

quote-evalNorm₁ : {n m : ℕ} → (c : n ⟷₁^ m) → quoteNorm₁ (⟷₁^-eq-size c) (evalNorm₁ c) ⟷₂^ c
quote-evalNorm₁ {O} c with (⟷₁^-eq-size c)
... | idp = trans⟷₂^ (c₊⟷₂id⟷₁ _) (!⟷₂^ (c₊⟷₂id⟷₁ c))
quote-evalNorm₁ {S n} p with (⟷₁^-eq-size p)
... | idp =
    let cancelSn : –> Fin≃Lehmer (<– Fin≃Lehmer (normpi2lehmer p)) == normpi2lehmer p
        cancelSn = <–-inv-r Fin≃Lehmer (normpi2lehmer p)

        sizes = (ℕ-S-is-inj _ _ (⟷₁^-eq-size p))
        
        cancelNorm : lehmer2normpi sizes (–> Fin≃Lehmer (<– Fin≃Lehmer (normpi2lehmer p))) ⟷₂^ p
        cancelNorm = transport (λ e -> lehmer2normpi sizes e ⟷₂^ p) (! cancelSn) (normpi2normpi p)

    in  cancelNorm

eval-quoteNorm₁ : {n : ℕ} → (p : Aut (Fin n)) → evalNorm₁ (quoteNorm₁ idp p) == p
eval-quoteNorm₁ {O} p = contr-has-all-paths {{Aut-FinO-level}} _ _
eval-quoteNorm₁ {S n} p =
    let cancelNorm : normpi2lehmer (lehmer2normpi idp (–> Fin≃Lehmer p)) == (–> Fin≃Lehmer p)
        cancelNorm = lehmer2lehmer (–> Fin≃Lehmer p)

        cancelSn : <– Fin≃Lehmer (normpi2lehmer (lehmer2normpi idp (–> Fin≃Lehmer p))) == p
        cancelSn = ap  (<– Fin≃Lehmer) cancelNorm ∙ <–-inv-l Fin≃Lehmer p

    in  cancelSn