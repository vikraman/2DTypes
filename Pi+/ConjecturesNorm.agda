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
    normpi2cox : {n m : ℕ} → ⟪ S n ⟫ ⟷₁ ⟪ S m ⟫ → Sn n
    cox2normpi : {n : ℕ} → Sn n → ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫

    normpi2normpi : {n m : ℕ} → (p : ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫) → cox2normpi (normpi2cox p) ⟷₂ p
    cox2cox : {n : ℕ} → (p : Sn n) → normpi2cox (cox2normpi p) == p
    
    ⟷₁-size : {n m : ℕ} → ⟪ n ⟫ ⟷₁ ⟪ m ⟫ → n == m


eval₁-norm : {n m : ℕ} → ⟪ n ⟫ ⟷₁ ⟪ m ⟫ → FinFS n == FinFS m
eval₁-norm {O} {O} p = idp
eval₁-norm {O} {S m} p = {!   !} -- ⊥ 
eval₁-norm {S n} {O} p = {!   !} -- ⊥ 
eval₁-norm {S n} {S m} p =
    let n=m : S n == S m
        n=m = ⟷₁-size p

        Fn=Fm = ap (λ e → FinFS e) n=m
        
        step1 : Sn n
        step1 = normpi2cox p

        step2 : FinFS (S n) == FinFS (S n)
        step2 = <– UFin≃Sn step1
    
    in  step2 ∙ Fn=Fm

quote₁-norm : {n m : ℕ} → (FinFS n) == (FinFS m) → ⟪ n ⟫ ⟷₁ ⟪ m ⟫
quote₁-norm {O} {O} p = id⟷₁
quote₁-norm {O} {S m} p = {!   !} -- ⊥ 
quote₁-norm {S n} {O} p = {!   !} -- ⊥ 
quote₁-norm {S n} {S m} p =
    let n=m : S n == S m
        n=m = Fin-inj (S n) (S m) (fst= p)

        Fn=Fm = ap (λ e → FinFS e) n=m
        
        step1 : Sn n
        step1 = –> UFin≃Sn (p ∙ ! Fn=Fm)

        step2 : ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫
        step2 = cox2normpi step1

    in  step2 ◎ transport (λ e → ⟪ S n ⟫ ⟷₁ ⟪ e ⟫) n=m id⟷₁

quote-eval₁-norm : {n m : ℕ} → (p : ⟪ n ⟫ ⟷₁ ⟪ m ⟫) → quote₁-norm (eval₁-norm p) ⟷₂ p
quote-eval₁-norm {O} {O} p = {!   !} -- obvious
quote-eval₁-norm {O} {S m} p = {!   !} -- ⊥ 
quote-eval₁-norm {S n} {O} p = {!   !} -- ⊥ 
quote-eval₁-norm {S n} {S m} p = {!   !}

eval-quote₁-norm : {n m : ℕ} → (p : FinFS n == FinFS m) → eval₁-norm (quote₁-norm p) == p
eval-quote₁-norm {O} {O} p = {!   !} -- obvious
eval-quote₁-norm {O} {S m} p = {!   !} -- ⊥ 
eval-quote₁-norm {S n} {O} p = {!   !} -- ⊥ 
eval-quote₁-norm {S n} {S m} p = {!   !}
