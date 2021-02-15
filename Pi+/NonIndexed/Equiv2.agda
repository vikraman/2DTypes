{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting --overlapping-instances #-}

module Pi+.NonIndexed.Equiv2 where

open import Pi+.Syntax as Pi
open import Pi+.UFin

open import Pi+.Extra

open import Pi+.Equiv0
open import Pi+.Equiv1

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct

eval₂ : {X Y : U} {p q : X ⟷₁ Y } → p ⟷₂ q → eval₁ p == eval₁ q
eval₂ {p = p} {q = q} α = TODO

quote₂ : {X Y : UFin} {p q : X == Y} (α : p == q) → quote₁ p ⟷₂ quote₁ q
quote₂ {p = p} {q = q} α = transport (λ e → quote₁ p ⟷₂ quote₁ e) α id⟷₂

quote-eval₂ : {X Y : U} {p q : X ⟷₁ Y } (α : p ⟷₂ q) → quote₂ (eval₂ α) ⟷₃
    trans⟷₂ (quote-eval₁ p) (trans⟷₂ (id⟷₂ ⊡ (α ⊡ id⟷₂)) (!⟷₂ (quote-eval₁ q)))
quote-eval₂ {p = p} {q = q} α = trunc (quote₂ (eval₂ α)) (trans⟷₂ (quote-eval₁ p) (trans⟷₂ (id⟷₂ ⊡ (α ⊡ id⟷₂)) (!⟷₂ (quote-eval₁ q))))

eval-quote₂ : {X Y : UFin} {p q : X == Y} (α : p == q) → eval₂ (quote₂ α) == ap (λ e → eval₁ (quote₁ e)) α
eval-quote₂ α = prop-has-all-paths _ _
