{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Equiv1Norm where

open import Pi+.Syntax as Pi
open import Pi+.UFin
open import Pi+.Level0
open import Pi+.Extra
open import Pi+.Equiv0

open import Pi+.Lehmer.Lehmer using (Lehmer)
open import Pi+.Lehmer.LehmerFinEquiv
open import Pi+.Coxeter.LehmerCoxeterEquiv
open import Pi+.Coxeter.Sn
open import Pi+.UFinLehmerEquiv

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct
open import lib.types.Sigma

lehmer2normpi : {n : ℕ} → Lehmer n → ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫
lehmer2normpi {n} cl = list2norm (immersion cl)

normpi2lehmer : {n : ℕ} → ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫ → Lehmer n
normpi2lehmer {n} p = immersion⁻¹ (norm2list p)

normpi2normpi : {n : ℕ} → (p : ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫) → lehmer2normpi (normpi2lehmer p) ⟷₂ p
normpi2normpi {n} p =
    let lemma : immersion (immersion⁻¹ (norm2list p)) ≈ (norm2list p)
        lemma = immersion∘immersion⁻¹ (norm2list p)
    in  trans⟷₂ (piRespectsCox _ _ _ lemma) (norm2norm p)

lehmer2lehmer : {n : ℕ} → (p : Lehmer n) → normpi2lehmer (lehmer2normpi p) == p
lehmer2lehmer {n} p = ap immersion⁻¹ (list2list (immersion p)) ∙ immersion⁻¹∘immersion p

eval₁-norm : {n : ℕ} → ⟪ n ⟫ ⟷₁ ⟪ n ⟫ → FinFS n == FinFS n
eval₁-norm {O} p = idp
eval₁-norm {S n} p =
    let step1 : Lehmer n
        step1 = normpi2lehmer p

        step2 : FinFS (S n) == FinFS (S n)
        step2 = <– UFin≃Lehmer step1

    in  step2

quote₁-norm : {n : ℕ} → (FinFS n) == (FinFS n) → ⟪ n ⟫ ⟷₁ ⟪ n ⟫
quote₁-norm {O} p = id⟷₁
quote₁-norm {S n} p =
    let step1 : Lehmer n
        step1 = –> UFin≃Lehmer p

        step2 : ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫
        step2 = lehmer2normpi step1

    in  step2

quote-eval₁-norm : {n : ℕ} → (p : ⟪ n ⟫ ⟷₁ ⟪ n ⟫) → quote₁-norm (eval₁-norm p) ⟷₂ p
quote-eval₁-norm {O} p = zero⟷₂ p
quote-eval₁-norm {S n} p =
    let cancelSn : –> UFin≃Lehmer (<– UFin≃Lehmer (normpi2lehmer p)) == normpi2lehmer p
        cancelSn = <–-inv-r UFin≃Lehmer (normpi2lehmer p)

        cancelNorm : lehmer2normpi (–> UFin≃Lehmer (<– UFin≃Lehmer (normpi2lehmer p))) ⟷₂ p
        cancelNorm = transport (λ e -> lehmer2normpi e ⟷₂ p) (! cancelSn) (normpi2normpi p)

    in  cancelNorm

eval-quote₁-norm : {n : ℕ} → (p : FinFS n == FinFS n) → eval₁-norm (quote₁-norm p) == p
eval-quote₁-norm {O} p = {!   !} -- obvious
eval-quote₁-norm {S n} p =
    let cancelNorm : normpi2lehmer (lehmer2normpi (–> UFin≃Lehmer p)) == (–> UFin≃Lehmer p)
        cancelNorm = lehmer2lehmer (–> UFin≃Lehmer p)

        cancelSn : <– UFin≃Lehmer (normpi2lehmer (lehmer2normpi (–> UFin≃Lehmer p))) == p
        cancelSn = ap  (<– UFin≃Lehmer) cancelNorm ∙ <–-inv-l UFin≃Lehmer p

    in  cancelSn
