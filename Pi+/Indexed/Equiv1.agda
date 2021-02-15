{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Indexed.Equiv1 where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^

open import Pi+.UFin
open import Pi+.Extra

open import Pi+.Indexed.Equiv0Norm
open import Pi+.Indexed.Equiv0Hat
open import Pi+.Indexed.Equiv0
open import Pi+.Indexed.Equiv1Norm
open import Pi+.Indexed.Equiv1Hat
open import Pi+.Indexed.Equiv2Norm
open import Pi+.Indexed.Equiv2Hat

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

eval₁ : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → Aut (Fin n)
eval₁ = evalNorm₁ ∘ eval^₁

quote₁ : {t₁ : U n} {t₂ : U m} → (p : n == m) → Aut (Fin n) → (t₁ ⟷₁ t₂)
quote₁ {t₁ = t₁} {t₂ = t₂} p e = 
    let c = quote^₁ {t₁ = eval^₀ t₁} {t₂ = eval^₀ t₂} (quoteNorm₁ p _ _ e)
    in  denorm← c

eval-quote₁ : (e : Aut (Fin n)) → (eval₁ {t₁ = (quote₀ (pFin _))} {t₂ = (quote₀ (pFin _))} (quote₁ idp e)) == e
eval-quote₁ {n} e = 
    let l1 = eval-quoteNorm₁ e
        l2 = eval-quote^₁ (quoteNorm₁ idp (quoteNorm₀ (pFin _)) (quoteNorm₀ (pFin _)) e)
        l3 = evalNorm₂ {n} {n} {_} {_} {_} {_} l2
    in  ({!   !} ∙ l3 ∙ {!   !}) ∙ l1 -- (l3 ∙ {!   !}) ∙ l1

postulate
    eq-size-rewrite : {t₁ : U n} {t₂ : U m} {c : t₁ ⟷₁ t₂} → (⟷₁^-eq-size (eval^₁ c)) ↦ (⟷₁-eq-size c) -- because proof of == in ℕ
    {-# REWRITE eq-size-rewrite #-}

quote-eval₁ : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → (quote₁ (⟷₁-eq-size c) (eval₁ c)) ⟷₂ denorm c
quote-eval₁ {t₁ = t₁} {t₂ = t₂} c = 
    let l1 = quote-eval^₁ c
        l2 = quote^₂ (quote-evalNorm₁ (eval^₁ c))
    in    _ 
        ⟷₂⟨ id⟷₂ ⊡ (l2 ⊡ id⟷₂) ⟩
          _
        ⟷₂⟨ !⟷₁⟷₂ (quote-eval²₀ t₁) ⊡ (id⟷₂ ⊡ quote-eval²₀ t₂) ⟩
          _
        ⟷₂⟨ id⟷₂ ⊡ idr◎l ⟩
          _
        ⟷₂⟨ idl◎l ⟩
          quote^₁ (eval^₁ c) 
        ⟷₂⟨ l1 ⟩
          denorm c 
        ⟷₂∎