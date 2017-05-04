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

open OneDimensionalTerms
⟦_⟧₂ : {A B : U} {p q : A ⟷₁ B} → (u : p ⟷₂ q) → ⟦ p ⟧₁ == ⟦ q ⟧₁
⟦_⟧₂ {p = p} `id₂ = refl ⟦ p ⟧₁
⟦_⟧₂ (`idl p) = ◾unitl ⟦ p ⟧₁
⟦_⟧₂ (`idr p) = ◾unitr ⟦ p ⟧₁
⟦_⟧₂ (`!l p) = ◾invr ⟦ p ⟧₁
⟦_⟧₂ (`!r p) = ◾invl ⟦ p ⟧₁
⟦_⟧₂ `!id = refl M.`id
⟦_⟧₂ `!not = !not=not
⟦_⟧₂ (`!◾ {p = p} {q}) = !◾ ⟦ p ⟧₁ ⟦ q ⟧₁
⟦_⟧₂ `!! = !! _
⟦_⟧₂ (`assoc p q r) = ◾assoc _ _ _
⟦_⟧₂ (!₂ u) = ! ⟦ u ⟧₂
⟦_⟧₂ (u ◾₂ u₁) = ⟦ u ⟧₂ ◾ ⟦ u₁ ⟧₂
⟦_⟧₂ (u □₂ v ) = ⟦ u ⟧₂ [2,0,2] ⟦ v ⟧₂
⟦_⟧₂ (`! α) = ap ! ⟦ α ⟧₂

open TwoDimensionalTerms
lem₃ : {p q r : M.`𝟚 == M.`𝟚} (p=r : p == r) (q=r : q == r) (u : p == q)
     → u == p=r ◾ ((! p=r) ◾ u ◾ q=r) ◾ (! q=r)
lem₃ p=r q=r u = (! (◾unitr u))
               ◾ ap (λ x → u ◾ x) (! (◾invr q=r))
               ◾ ! (◾unitl (u ◾ q=r ◾ ! q=r))
               ◾ ap (λ x → x ◾ u ◾ q=r ◾ ! q=r) (! (◾invr p=r))
               ◾ ◾assoc _ _ _
               ◾ ap (λ x → p=r ◾ x) (! (◾assoc _ _ _))
               ◾ ap (λ x → p=r ◾ x) (! (◾assoc _ _ _))
               ◾ ap (λ x → p=r ◾ x ◾ ! q=r) (◾assoc _ _ _)

⟦_⟧₃ : {A B : U} {p q : A ⟷₁ B} {u v : p ⟷₂ q} → (α : u ⟷₃ v) → ⟦ u ⟧₂ == ⟦ v ⟧₂
⟦_⟧₃ {U.`𝟚} {U.`𝟚} {p} {q} {u} {v} `trunc
     with all-1-paths ⟦ p ⟧₁ | all-1-paths ⟦ q ⟧₁
⟦_⟧₃ {U.`𝟚} {U.`𝟚} {p} {q} {u} {v} `trunc | i₁ p=id  | (i₁ q=id)  =
     lem₃ p=id q=id ⟦ u ⟧₂ ◾ ap (λ x → p=id ◾ x ◾ ! q=id) (all-2-paths-id _ ◾ (! (all-2-paths-id _))) ◾ ! (lem₃ p=id q=id ⟦ v ⟧₂)
⟦_⟧₃ {U.`𝟚} {U.`𝟚} {p} {q} {u} {v} `trunc | i₁ p=id  | (i₂ q=not) = rec𝟘 _ (¬id=not ((! p=id) ◾ ⟦ u ⟧₂ ◾ q=not))
⟦_⟧₃ {U.`𝟚} {U.`𝟚} {p} {q} {u} {v} `trunc | i₂ p=not | (i₁ q=id)  = rec𝟘 _ (¬id=not ((! q=id) ◾ ! ⟦ u ⟧₂ ◾ p=not))
⟦_⟧₃ {U.`𝟚} {U.`𝟚} {p} {q} {u} {v} `trunc | i₂ p=not | (i₂ q=not) =
     lem₃ p=not q=not ⟦ u ⟧₂ ◾ ap (λ x → p=not ◾ x ◾ ! q=not) (all-2-paths-not _ ◾ (! (all-2-paths-not _))) ◾ ! (lem₃ p=not q=not ⟦ v ⟧₂)

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

  -- canonical 2
  -- canonical 3

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
  ... | NOT , α | NOT , β = ID , ((α □₂ β) ◾₂ (((!₂ `!not) □₂ `id₂) ◾₂ (`!r _⟷₁_.`not)))
