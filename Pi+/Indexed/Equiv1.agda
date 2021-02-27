{-# OPTIONS --without-K --exact-split --rewriting #-}

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

import Pi+.Coxeter.LehmerCoxeterEquiv
import Pi+.Lehmer.LehmerFinEquiv

private
    variable
        n m : ℕ

eval₁ : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → Aut (Fin n)
eval₁ = evalNorm₁ ∘ eval^₁

quote₁ : {t₁ : U n} {t₂ : U m} → (p : n == m) → Aut (Fin n) → (t₁ ⟷₁ t₂)
quote₁ {t₁ = t₁} {t₂ = t₂} p e =
    let c = quote^₁ {n = eval^₀ t₁} {m = eval^₀ t₂} (quoteNorm₁ p e)
    in  denorm← c

-- postulate
    -- eq-size-rewrite0 : {t₁ t₂ : U n} {c : t₁ ⟷₁ t₂} → (⟷₁-eq-size (quote^₁ (eval^₁ c))) ↦ idp -- because proof of == in ℕ
    -- norm2list-rewrite : norm2list (⊕^ (id⟷₁^ {n = n})) ↦ nil
    -- {-# REWRITE eq-size-rewrite0 norm2list-rewrite #-}
  -- rewrite (ℕ-p (+-assoc 1 0 n))
  -- rewrite (ℕ-p (+-unit-r 0))
  -- rewrite (ℕ-p (+-unit-r 1))
  -- rewrite (ℕ-p (+-assoc 0 0 1)) =

eval-quote₁ : (e : Aut (Fin n)) → (eval₁ {t₁ = (quote₀ (pFin _))} {t₂ = (quote₀ (pFin _))} (quote₁ idp e)) == e
eval-quote₁ {O} e = contr-has-all-paths {{Aut-FinO-level}} _ _
eval-quote₁ {S n} e =
    let l1 = eval-quoteNorm₁ e
        l2 = eval-quote^₁ (quoteNorm₁ idp e)
        l3 = evalNorm₂ l2
    in  (TODO ∙ l3) ∙ l1 -- this should evaluate to idp when we have TODOs in Pi_.Misc filled in

postulate
    eq-size-rewrite : {t₁ : U n} {t₂ : U m} {c : t₁ ⟷₁ t₂} → (⟷₁^-eq-size (eval^₁ c)) ↦ (⟷₁-eq-size c) -- because proof of == in ℕ
    {-# REWRITE eq-size-rewrite #-}

quote-eval²₀ : (t : U n) → quote-eval^₀ (quote^₀ (eval^₀ t)) ⟷₂ id⟷₁
quote-eval²₀ {O} t = id⟷₂
quote-eval²₀ {S n} t =
  let rec = quote-eval²₀ {n} (quote₀ (pFin _))
  in  _
    ⟷₂⟨ id⟷₂ ⊡ resp⊕⟷₂ id⟷₂ rec ⟩
      _
    ⟷₂⟨ TODO ⟩ -- Goal: (((id⟷₁ ⊕ uniti₊l) ◎ assocl₊) ◎ unite₊r ⊕ id⟷₁) ⟷₂ id⟷₁
      _
    ⟷₂∎

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
