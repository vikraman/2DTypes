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
⟦_⟧₂ (u □₂ v ) = ⟦ u ⟧₂ [2,0,2] ⟦ v ⟧₂
⟦_⟧₂ (`! α) = ap ! ⟦ α ⟧₂

-- One approach to completeness:
module Altenkich where
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

  ------------------------------------------------------------------------------
  -- Normalization by evaluation a la Altenkirch

  canonical₁ : {A B : U} → (p : A ⟷₁ B) → (A ⟷₁ B)
  canonical₁ p = quote₁ ⟦ p ⟧₁

  inversion₁ : {A B : U} → (p : A ⟷₁ B) → canonical₁ p ⟷₂ p
  inversion₁ {U.`𝟚} {.U.`𝟚} _⟷₁_.`id = `id₂
  inversion₁ {U.`𝟚} {.U.`𝟚} _⟷₁_.`not = {!!} -- lack of evaluation blocks
  inversion₁ (!₁ u) = {!!}
  inversion₁ (u ◾₁ u₁) = {!!}

  completeness₁ : {A B : U} {p q : A ⟷₁ B} → ⟦ p ⟧₁ == ⟦ q ⟧₁ → p ⟷₂ q
  completeness₁ {p = p} {q = q} u = {!!}
  {--
  p <=> canonical p <=> canonical q <=> q
  --}

------------------------------------------------------------------------------

-- Another approach
module Direct where
  open _⟷₁_

  data Which : Set₀ where ID NOT : Which

  refine : (w : Which) → U.`𝟚 ⟷₁ U.`𝟚
  refine ID = _⟷₁_.`id
  refine NOT = _⟷₁_.`not

  canonical₁ : (p : U.`𝟚 ⟷₁ U.`𝟚) → Σ Which (λ c → p ⟷₂ (refine c))
  canonical₁ `id = ID , `id₂
  canonical₁ `not = NOT , `id₂
  canonical₁ (!₁ p) with canonical₁ p
  ... | ID  , α = ID  , (`! α ◾₂ `!id)
  ... | NOT , α = NOT , (`! α ◾₂ `!not)
  canonical₁ (_◾₁_ {_} {U.`𝟚} p₀ p₁) with canonical₁ p₀ | canonical₁ p₁
  ... | ID  , α | ID  , β = ID , ((α □₂ β) ◾₂ `idl _⟷₁_.`id)
  ... | ID  , α | NOT , β = NOT , ((α □₂ β) ◾₂ `idl _⟷₁_.`not)
  ... | NOT , α | ID  , β = NOT , ((α □₂ β) ◾₂ `idr _⟷₁_.`not)
  ... | NOT , α | NOT , β = ID , ((α □₂ β) ◾₂ {!`!!!})
