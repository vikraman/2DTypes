{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Equiv1 where

open import Pi+.Syntax as Pi
open import Pi+.UFin
open import Pi+.Level0
open import Pi+.Extra

open import Pi+.Lehmer.Lehmer

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


norm : {X Y : U} → X ⟷₁ Y → ⟪ ∣ X ∣ ⟫ ⟷₁ ⟪ ∣ Y ∣ ⟫
norm {X} {Y} p = quote-eval₀ X ◎ p ◎ !⟷₁ (quote-eval₀ Y)

denorm : {X Y : U} → ⟪ ∣ X ∣ ⟫ ⟷₁ ⟪ ∣ Y ∣ ⟫ → X ⟷₁ Y
denorm {X} {Y} p = (!⟷₁ (quote-eval₀ X)) ◎ p ◎ (quote-eval₀ Y)

postulate
    denorm∘norm : {X Y : U} → (c : X ⟷₁ Y) → denorm (norm c) ⟷₂ c
    norm∘denorm : {X Y : U} → (c : ⟪ ∣ X ∣ ⟫ ⟷₁ ⟪ ∣ Y ∣ ⟫) → norm {X} {Y} (denorm c) ⟷₂ c

finfs-ufin : {X Y : UFin} -> (FinFS (card X) == FinFS (card Y)) ≃ (X == Y)
finfs-ufin = equiv (λ x → {!   !}) (λ {idp → idp}) (λ {idp → {!   !}}) (λ {b → {!   !}})

⟷₁-size : {n m : ℕ} → ⟪ n ⟫ ⟷₁ ⟪ m ⟫ → n == m
⟷₁-size {n} {m} p = 
    let p = eqsize p
    in  ! ∣⟪ n ⟫∣ ∙ p ∙ ∣⟪ m ⟫∣

eval₁ : {X Y : U} → X ⟷₁ Y → eval₀ X == eval₀ Y
eval₁ {X} {Y} p =
    let normp = norm p
        X=Y = ⟷₁-size normp  -- equality in Nat
        ide = ap FinFS X=Y
        idc = transport (λ e -> ⟪ ∣ Y ∣ ⟫ ⟷₁ ⟪ e ⟫) (! X=Y) id⟷₁
        
        evc = eval₁-norm (normp ◎ idc)
    in  evc ∙ ide

quote₁ : {X Y : UFin} → X == Y → quote₀ X ⟷₁ quote₀ Y
quote₁ {X} {Y} p =
    let normp = <– finfs-ufin p
        X=Y = ap card p -- equality in Nat
        ide = ap FinFS X=Y
        idc = transport (λ e -> ⟪ card X ⟫ ⟷₁ ⟪ e ⟫) X=Y id⟷₁

        evc = quote₁-norm (normp ∙ ! ide)
    in  evc ◎ idc

quote-eval₁ : {X Y : U} → (p : X ⟷₁ Y) → quote₁ (eval₁ p) ⟷₂ norm p
quote-eval₁ {X} {Y} p =
    let normp = norm p
        X=Y = ⟷₁-size normp  -- equality in Nat
        ide = ap FinFS X=Y
        idc = transport (λ e -> ⟪ ∣ Y ∣ ⟫ ⟷₁ ⟪ e ⟫) (! X=Y) id⟷₁
        
        evc = eval₁-norm (normp ◎ idc)
        p' = evc ∙ ide
        
        normp' = <– finfs-ufin p'
        X=Y' = ap card p' -- equality in Nat
        ide' = ap FinFS X=Y'
        idc' = transport (λ e -> ⟪ card (eval₀ X) ⟫ ⟷₁ ⟪ e ⟫) X=Y' id⟷₁

        evc' = quote₁-norm (normp' ∙ ! ide')
        p'' = evc' ◎ idc'
        
        quoted⟷₂norm : p'' ⟷₂ (quote-eval₀ X ◎ p ◎ !⟷₁ (quote-eval₀ Y))
        quoted⟷₂norm = {!   !}
        
    in  quoted⟷₂norm

eval-quote₁ : {X Y : UFin} → (p : X == Y) → eval₁ (quote₁ p) == ap (λ X → eval₀ (quote₀ X)) p
eval-quote₁ p = TODO