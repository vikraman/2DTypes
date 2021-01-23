{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Equiv1 where

open import Pi+.Syntax as Pi
open import Pi+.UFin
open import Pi+.Level0
open import Pi+.Extra

open import Pi+.Coxeter.Common.Lehmer
open import Pi+.Coxeter.Parametrized.Equiv

open import Pi+.Equiv0
open import Pi+.Equiv1Norm

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct
open import lib.types.Sigma

postulate
    norm : {X Y : U} → X ⟷₁ Y → ⟪ ∣ X ∣ ⟫ ⟷₁ ⟪ ∣ Y ∣ ⟫
    denorm : {X Y : U} → ⟪ ∣ X ∣ ⟫ ⟷₁ ⟪ ∣ Y ∣ ⟫ → X ⟷₁ Y

    denorm∘norm : {X Y : U} → (c : X ⟷₁ Y) → denorm (norm c) ⟷₂ c
    norm∘denorm : {X Y : U} → (c : ⟪ ∣ X ∣ ⟫ ⟷₁ ⟪ ∣ Y ∣ ⟫) → norm {X} {Y} (denorm c) ⟷₂ c

    ⟷₁-size : {n m : ℕ} → ⟪ n ⟫ ⟷₁ ⟪ m ⟫ → m == n

eval₁ : {X Y : U} → X ⟷₁ Y → eval₀ X == eval₀ Y
eval₁ {X} {Y} p = 
    let normc = norm p
        Y=X = ⟷₁-size normc
        evc = eval₁-norm (transport (λ e -> ⟪ ∣ X ∣ ⟫ ⟷₁ ⟪ e ⟫ ) Y=X normc)
    in  evc ∙ ! (ap FinFS Y=X)

quote₁ : {X Y : UFin} → X == Y → quote₀ X ⟷₁ quote₀ Y
quote₁ {X} {Y} p = 
    let X=Y : card X == card Y
        X=Y = ap card p

        evc : quote₀ X ⟷₁ quote₀ X
        evc = quote₁-norm {!  !} -- p ∙ ?

    in  evc ◎ transport (λ e -> quote₀ X ⟷₁ e) (ap ⟪_⟫ X=Y) id⟷₁ -- does it matter over which X=Y do I transport?

quote-eval₁ : {X Y : U} → (p : X ⟷₁ Y) → quote₁ (eval₁ p) ⟷₂ (quote-eval₀ X ◎ p ◎ !⟷₁ (quote-eval₀ Y))
quote-eval₁ p = TODO

eval-quote₁ : {X Y : UFin} → (p : X == Y) → eval₁ (quote₁ p) == ap (λ X → eval₀ (quote₀ X)) p
eval-quote₁ p = TODO