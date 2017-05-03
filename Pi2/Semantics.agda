{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Pi2.Semantics where

open import UnivalentTypeTheory
open import TwoUniverse as M
open import Pi2.Syntax as S

------------------------------------------------------------------------------
-- Soundness: mapping syntax to the model

⟦_⟧ : U → U[𝟚]
⟦ `𝟚 ⟧ = M.`𝟚

⟦_⟧₁ : {A B : U} → A ⟷₁ B → ⟦ A ⟧ == ⟦ B ⟧
⟦_⟧₁ `id = M.`id
⟦_⟧₁ `not = M.`not
⟦_⟧₁ (!₁ p) = ! ⟦ p ⟧₁
⟦_⟧₁ (p ◾₁ q) = ⟦ p ⟧₁ ◾ ⟦ q ⟧₁

⟦_⟧₂ : {A B : U} {p q : A ⟷₁ B} → (u : p ⟷₂ q) → ⟦ p ⟧₁ == ⟦ q ⟧₁
⟦_⟧₂ {p = p} `id₂ = refl ⟦ p ⟧₁
⟦_⟧₂ (`idl p) = ◾unitl ⟦ p ⟧₁
⟦_⟧₂ (`idr p) = ◾unitr ⟦ p ⟧₁
⟦_⟧₂ (`!l p) = ◾invr ⟦ p ⟧₁
⟦_⟧₂ (`!r p) = ◾invl ⟦ p ⟧₁
⟦_⟧₂ `!id = refl M.`id
⟦_⟧₂ `!not = M.OneDimensionalTerms.!not=not
⟦_⟧₂ (`!◾ {p = p} {q}) = !◾ ⟦ p ⟧₁ ⟦ q ⟧₁
⟦_⟧₂ `!! = !! _
⟦_⟧₂ (`assoc p q r) = ◾assoc _ _ _
⟦_⟧₂ (!₂ u) = ! ⟦ u ⟧₂
⟦_⟧₂ (u ◾₂ u₁) = ⟦ u ⟧₂ ◾ ⟦ u₁ ⟧₂
⟦_⟧₂ (_□₂_ {u = u} {v}) = ⟦ u ⟧₂ [2,0,2] ⟦ v ⟧₂

⟦_⟧₃ : {A B : U} {p q : A ⟷₁ B} {u v : p ⟷₂ q} → (α : u ⟷₃ v) → ⟦ u ⟧₂ == ⟦ v ⟧₂
⟦ `trunc ⟧₃ = {!!}

------------------------------------------------------------------------------
-- Completeness: mapping the model to syntax

quote₀ : U[𝟚] → U
quote₀ _ = U.`𝟚

quote₁ : {A B : U} → ⟦ A ⟧ == ⟦ B ⟧ → A ⟷₁ B
quote₁ {U.`𝟚} {U.`𝟚} eq with M.OneDimensionalTerms.all-1-paths eq
... | i₁ _ = _⟷₁_.`id
... | i₂ _ = _⟷₁_.`not

quote₂ : {A B : U} {p q : A ⟷₁ B} → ⟦ p ⟧₁ == ⟦ q ⟧₁ → (p ⟷₂ q)
quote₂ eq₂ = {!!}

quote₃ : {A B : U} {p q : A ⟷₁ B} {u v : p ⟷₂ q} → ⟦ u ⟧₂ == ⟦ v ⟧₂ → (u ⟷₃ v)
quote₃ _ = `trunc

------------------------------------------------------------------------------
-- Normalization by evaluation a la Altenkirch

canonical₁ : {A B : U} → (p : A ⟷₁ B) → (A ⟷₁ B)
canonical₁ p = quote₁ ⟦ p ⟧₁

canonical-resp : {A B : U} {p q : A ⟷₁ B} → (⟦ p ⟧₁ == ⟦ q ⟧₁) →
                 canonical₁ p ⟷₂ canonical₁ q
canonical-resp eq = {!!}

inversion₁ : {A B : U} → (p : A ⟷₁ B) → canonical₁ p ⟷₂ p
inversion₁ {U.`𝟚} {.U.`𝟚} _⟷₁_.`id = `id₂
inversion₁ {U.`𝟚} {.U.`𝟚} _⟷₁_.`not = {!`id₂!} -- lack of evaluation blocks
inversion₁ (!₁ u) = {!!}
inversion₁ (u ◾₁ u₁) = {!!}

completeness₁ : {A B : U} {p q : A ⟷₁ B} → ⟦ p ⟧₁ == ⟦ q ⟧₁ → p ⟷₂ q
completeness₁ {p = p} {q = q} u =
  (!₂ (inversion₁ p)) ◾₂ (canonical-resp {p = p} {q = q} u ◾₂ (inversion₁ q))

------------------------------------------------------------------------------
