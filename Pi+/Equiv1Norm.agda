{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Equiv1Norm where

open import Pi+.Syntax as Pi
open import Pi+.UFin
open import Pi+.Level0
open import Pi+.Extra
open import Pi+.Equiv0

open import Pi+.Coxeter.Common.Lehmer
open import Pi+.Coxeter.Parametrized.Equiv
open import Pi+.Coxeter.Parametrized.Group

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct
open import lib.types.Sigma

postulate
    pi2list : {n : ℕ} → ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫ → List (Fin n)
    list2pi : {n : ℕ} → (List (Fin n)) → ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫

    pi2pi : {n : ℕ} → (p : ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫) → list2pi (pi2list p) ⟷₂ p
    list2list : {n : ℕ} → (p : List (Fin n)) → pi2list (list2pi p) == p

lehmer2pi : {n : ℕ} → Lehmer n → ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫
lehmer2pi {n} cl = list2pi (immersionFin cl)

normpi2cox : {n : ℕ} → ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫ → Sn n
normpi2cox {n} p = q[ pi2list p ]

cox2normpi : {n : ℕ} → Sn n → ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫
cox2normpi {n} = SetQuot-elim {{{!   !}}} (λ l → lehmer2pi (<– Lehmer≃Sn q[ l ])) {!   !}

normpi2normpi : {n : ℕ} → (p : ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫) → cox2normpi (normpi2cox p) ⟷₂ p
normpi2normpi {n} p = {!   !}

cox2cox : {n : ℕ} → (p : Sn n) → normpi2cox (cox2normpi p) == p
cox2cox {n} p = {!   !}

eval₁-norm : {n : ℕ} → ⟪ n ⟫ ⟷₁ ⟪ n ⟫ → FinFS n == FinFS n
eval₁-norm {O} p = idp
eval₁-norm {S n} p =
    let step1 : Sn n
        step1 = normpi2cox p

        step2 : FinFS (S n) == FinFS (S n)
        step2 = <– UFin≃Sn step1
    
    in  step2

quote₁-norm : {n : ℕ} → (FinFS n) == (FinFS n) → ⟪ n ⟫ ⟷₁ ⟪ n ⟫
quote₁-norm {O} p = id⟷₁
quote₁-norm {S n} p =
    let step1 : Sn n
        step1 = –> UFin≃Sn p

        step2 : ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫
        step2 = cox2normpi step1

    in  step2

quote-eval₁-norm : {n : ℕ} → (p : ⟪ n ⟫ ⟷₁ ⟪ n ⟫) → quote₁-norm (eval₁-norm p) ⟷₂ p
quote-eval₁-norm {O} p = TODO -- obvious
quote-eval₁-norm {S n} p = 
    let cancelSn : –> UFin≃Sn (<– UFin≃Sn (normpi2cox p)) == normpi2cox p
        cancelSn = <–-inv-r UFin≃Sn (normpi2cox p)

        cancelNorm : cox2normpi (–> UFin≃Sn (<– UFin≃Sn (normpi2cox p))) ⟷₂ p
        cancelNorm = transport (λ e -> cox2normpi e ⟷₂ p) (! cancelSn) (normpi2normpi p)

    in  cancelNorm

eval-quote₁-norm : {n : ℕ} → (p : FinFS n == FinFS n) → eval₁-norm (quote₁-norm p) == p
eval-quote₁-norm {O} p = TODO -- obvious
eval-quote₁-norm {S n} p = 
    let cancelNorm : normpi2cox (cox2normpi (–> UFin≃Sn p)) == (–> UFin≃Sn p)
        cancelNorm = cox2cox (–> UFin≃Sn p)

        cancelSn : <– UFin≃Sn (normpi2cox (cox2normpi (–> UFin≃Sn p))) == p
        cancelSn = ap  (<– UFin≃Sn) cancelNorm ∙ <–-inv-l UFin≃Sn p
        
    in  cancelSn
