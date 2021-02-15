{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting --overlapping-instances #-}

module Pi+.Indexed.Equiv2 where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.UFin
open import Pi+.Level0
open import Pi+.Extra
open import Pi+.UFin.BAut

open import Pi+.Indexed.Equiv0
open import Pi+.Indexed.Equiv1
open import Pi+.Indexed.Equiv2Norm
open import Pi+.Indexed.Equiv2Hat

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct

private
    variable
        n m : ℕ

eval₂ : {t₁ t₂ : U n} {c₁ c₂ : t₁ ⟷₁ t₂} → c₁ ⟷₂ c₂ → eval₁ c₁ == eval₁ c₂
eval₂ = evalNorm₂ ∘ eval^₂

quote₂ : {t₁ t₂ : U n} {e₁ e₂ : Aut (Fin n)} (α : e₁ == e₂) → quote₁ {t₁ = t₁} {t₂ = t₂} idp e₁ ⟷₂ quote₁ {t₁ = t₁} {t₂ = t₂} idp e₂
quote₂ {n} {t₁ = t₁} {t₂ = t₂} {e₁ = e₁} {e₂ = e₂} α = transport (λ e → _⟷₂_ {n} {n} {t₁} {t₂} (quote₁ idp e₁) (quote₁ idp e)) α id⟷₂

postulate
    eq-size-idp-rewrite : {t₁ : U n} {t₂ : U n} {c : t₁ ⟷₁ t₂} → (⟷₁-eq-size c) ↦ idp -- because proof of == in ℕ
    {-# REWRITE eq-size-idp-rewrite #-}

quote-eval₂ : {t₁ t₂ : U n} {c₁ c₂ : t₁ ⟷₁ t₂} (α : c₁ ⟷₂ c₂) → quote₂ (eval₂ α) ⟷₃ trans⟷₂ (quote-eval₁ c₁) (trans⟷₂ (id⟷₂ ⊡ (α ⊡ id⟷₂)) (!⟷₂ (quote-eval₁ c₂)))
quote-eval₂ {c₁ = c₁} {c₂ = c₂} α = trunc _ _

eval-quote₂ : {e₁ e₂ : Aut (Fin n)} (α : e₁ == e₂) → 
    eval₂ {t₁ = quote₀ (pFin _)} {t₂ = quote₀ (pFin _)} (quote₂ α) == ap (λ e → (eval₁ (quote₁ {t₁ = quote₀ (pFin _)} {t₂ = quote₀ (pFin _)} idp e))) α
eval-quote₂ α = prop-has-all-paths {{has-level-apply (Aut-level {{Fin-is-set}}) _ _}} _ _
