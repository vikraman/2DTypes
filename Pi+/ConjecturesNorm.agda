{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.ConjecturesNorm where

open import Pi+.Syntax as Pi
open import Pi+.UFin
open import Pi+.Level0
open import Pi+.Extra
open import Pi+.Conjectures

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
    normpi2cox : {n : ℕ} → ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫ → Sn n
    cox2normpi : {n : ℕ} → Sn n → ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫

    normpi2normpi : {n : ℕ} → (p : ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫) → cox2normpi (normpi2cox p) ⟷₂ p
    cox2cox : {n : ℕ} → (p : Sn n) → normpi2cox (cox2normpi p) == p
    
    ⟷₁-size : {n m : ℕ} → ⟪ n ⟫ ⟷₁ ⟪ m ⟫ → n == m


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
quote-eval₁-norm {O} p = {!   !} -- obvious
quote-eval₁-norm {S n} p = {!   !}

eval-quote₁-norm : {n : ℕ} → (p : FinFS n == FinFS n) → eval₁-norm (quote₁-norm p) == p
eval-quote₁-norm {O} p = {!   !} -- obvious
eval-quote₁-norm {S n} p = {!   !}
