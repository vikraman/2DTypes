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
⟦_⟧₁ {`𝟚} {`𝟚} `id = M.`id
⟦_⟧₁ {`𝟚} {`𝟚} `not = M.`not
⟦_⟧₁ {`𝟚} {`𝟚} (!₁ p) = ! ⟦ p ⟧₁
⟦_⟧₁ {`𝟚} {`𝟚} (p ◾₁ q) = ⟦ p ⟧₁ ◾ ⟦ q ⟧₁

-- Why?
⟦!_⟧₁≡ : {A B : U} → (p : A ⟷₁ B) → ⟦ !₁ p ⟧₁ == ! ⟦ p ⟧₁
⟦! p ⟧₁≡  = {!!}

⟦_◾_⟧₁≡ : {A B C : U} → (p : A ⟷₁ B) (q : B ⟷₁ C)→ ⟦ p ◾₁ q ⟧₁ == ⟦ p ⟧₁ ◾ ⟦ q ⟧₁
⟦ p ◾ q ⟧₁≡ = {!!}

⟦_⟧₂ : {A B : U} {p q : A ⟷₁ B} → (u : p ⟷₂ q) → ⟦ p ⟧₁ == ⟦ q ⟧₁
⟦_⟧₂ {U.`𝟚} {U.`𝟚} {p} `id₂ = refl ⟦ p ⟧₁
⟦_⟧₂ {U.`𝟚} {U.`𝟚} (`idl p) = ◾unitl ⟦ p ⟧₁
⟦_⟧₂ {U.`𝟚} {U.`𝟚} (`idr p) = ◾unitr ⟦ p ⟧₁
⟦_⟧₂ {U.`𝟚} {U.`𝟚} (`!l p) = (ap (λ x → ⟦ p ⟧₁ ◾ x) ⟦! p ⟧₁≡) ◾ ◾invr ⟦ p ⟧₁ ◾ refl (refl M.`𝟚)
⟦_⟧₂ {U.`𝟚} {U.`𝟚} (`!r p) = (ap (λ x → x ◾ ⟦ p ⟧₁) ⟦! p ⟧₁≡) ◾ ◾invl ⟦ p ⟧₁ ◾ refl (refl M.`𝟚)
⟦_⟧₂ {U.`𝟚} {U.`𝟚} `!id = refl (refl M.`𝟚)
⟦_⟧₂ {U.`𝟚} {U.`𝟚} `!not = {!!}
⟦_⟧₂ {U.`𝟚} {U.`𝟚} (`!◾ {A} {B} {C} {p} {q}) =
     (!◾ _ _) ◾ (ap (λ x → x ◾ ! ⟦ p ⟧₁) (! ⟦! q ⟧₁≡)) ◾ (ap (λ x → ⟦ !₁ q ⟧₁ ◾ x) (! ⟦! p ⟧₁≡))
⟦_⟧₂ {U.`𝟚} {U.`𝟚} `!! = !! _
⟦_⟧₂ {U.`𝟚} {U.`𝟚} (`assoc p q r) =
     (ap (λ x → x ◾ ⟦ r ⟧₁) ⟦ p ◾ q ⟧₁≡) ◾ ◾assoc ⟦ p ⟧₁ ⟦ q ⟧₁ ⟦ r ⟧₁ ◾ (ap (λ x → ⟦ p ⟧₁ ◾ x) (! ⟦ q ◾ r ⟧₁≡))
⟦_⟧₂ {U.`𝟚} {U.`𝟚} (!₂ u) = ! ⟦ u ⟧₂
⟦_⟧₂ {U.`𝟚} {U.`𝟚} (_◾₂_ u v) = ⟦ u ⟧₂ ◾ ⟦ v ⟧₂
⟦_⟧₂ {U.`𝟚} {U.`𝟚} (_□₂_ {A} {B} {C} {p} {q} {r} {s} {u} {v}) =
     (ap (λ x → x ◾ ⟦ r ⟧₁) ⟦ u ⟧₂) ◾ ((ap (λ x → ⟦ q ⟧₁ ◾ x) ⟦ v ⟧₂))

{--
⟦-⟧₁-resp-idl : {A B : U} {p : A ⟷₁ B} → ⟦ S.`id ◾₁ p ⟧₁ == ⟦ p ⟧₁
⟦-⟧₁-resp-idl {p = `id} = {!!}
⟦-⟧₁-resp-idl {p = `not} = {!!}
⟦-⟧₁-resp-idl {p = !₁ p} = {!!}
⟦-⟧₁-resp-idl {p = p ◾₁ q} = {!!}

⟦-⟧₁-resp-idr : {A B : U} {p : A ⟷₁ B} → ⟦ p ◾₁ S.`id ⟧₁ == ⟦ p ⟧₁
⟦-⟧₁-resp-idr {p = `id} = {!!}
⟦-⟧₁-resp-idr {p = `not} = {!!}
⟦-⟧₁-resp-idr {p = !₁ p} = {!!}
⟦-⟧₁-resp-idr {p = p ◾₁ q} = {!!}

⟦-⟧₁-resp-◾ : {A B C : U} {p : A ⟷₁ B} {q : B ⟷₁ C} → ⟦ p ◾₁ q ⟧₁ == ⟦ p ⟧₁ ◾ ⟦ q ⟧₁
⟦-⟧₁-resp-◾ = {!!}
--}

------------------------------------------------------------------------------
-- Completeness: mapping the model to syntax

quote₀ : U[𝟚] → U
quote₀ _ = U.`𝟚

quote₁ : {A B : U} → ⟦ A ⟧ == ⟦ B ⟧ → A ⟷₁ B
quote₁ eq = {!!}

quote₂ : {A B : U} {p q : A ⟷₁ B} → ⟦ p ⟧₁ == ⟦ q ⟧₁ → (p ⟷₂ q)
quote₂ eq₂ = {!!}

------------------------------------------------------------------------------
-- Normalization by evaluation a la Altenkirch

canonical₁ : {A B : U} → (p : A ⟷₁ B) → (A ⟷₁ B)
canonical₁ p = quote₁ ⟦ p ⟧₁

inversion₁ : {A B : U} → (p : A ⟷₁ B) → canonical₁ p ⟷₂ p
inversion₁ u = {!!}

completeness₁ : {A B : U} {p q : A ⟷₁ B} → ⟦ p ⟧₁ == ⟦ q ⟧₁ → p ⟷₂ q
completeness₁ {p = p} {q = q} u = {!!}
{--
p <=> canonical p <=> canonical q <=> q
--}

------------------------------------------------------------------------------
