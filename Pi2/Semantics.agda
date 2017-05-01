{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Pi2.Semantics where

open import UnivalentTypeTheory
open import TwoUniverse as M
open import Pi2.Syntax as S

⟦_⟧ : U → U[𝟚]
⟦ `𝟚 ⟧ = M.`𝟚

⟦_⟧₁ : {A B : U} → A ⟷₁ B → ⟦ A ⟧ == ⟦ B ⟧
⟦_⟧₁ {`𝟚} {`𝟚} `id = M.`id
⟦_⟧₁ {`𝟚} {`𝟚} `not = M.`not
⟦_⟧₁ {`𝟚} {`𝟚} (!₁ p) = ! ⟦ p ⟧₁
⟦_⟧₁ {`𝟚} {`𝟚} (p ◾₁ q) = ⟦ p ⟧₁ ◾ ⟦ q ⟧₁

⟦-⟧₁-resp-idl : {A B : U} {p : A ⟷₁ B} → ⟦ `id₁ ◾₁ p ⟧₁ == ⟦ p ⟧₁
⟦-⟧₁-resp-idl {p = `id} = {!!}
⟦-⟧₁-resp-idl {p = `not} = {!!}
⟦-⟧₁-resp-idl {p = !₁ p} = {!!}
⟦-⟧₁-resp-idl {p = p ◾₁ q} = {!!}

⟦-⟧₁-resp-idr : {A B : U} {p : A ⟷₁ B} → ⟦ p ◾₁ `id₁ ⟧₁ == ⟦ p ⟧₁
⟦-⟧₁-resp-idr {p = `id} = {!!}
⟦-⟧₁-resp-idr {p = `not} = {!!}
⟦-⟧₁-resp-idr {p = !₁ p} = {!!}
⟦-⟧₁-resp-idr {p = p ◾₁ q} = {!!}

⟦-⟧₁-resp-◾ : {A B C : U} {p : A ⟷₁ B} {q : B ⟷₁ C} → ⟦ p ◾₁ q ⟧₁ == ⟦ p ⟧₁ ◾ ⟦ q ⟧₁
⟦-⟧₁-resp-◾ = {!!}

⟦_⟧₂ : {A B : U} {p q : A ⟷₁ B} → (u : p ⟷₂ q) → ⟦ p ⟧₁ == ⟦ q ⟧₁
⟦_⟧₂ {`𝟚} {`𝟚} (`idl p) = {!!}
⟦_⟧₂ {`𝟚} {`𝟚} (`idr p) = {!!}
⟦_⟧₂ {`𝟚} {`𝟚} (`!l p) = {!!}
⟦_⟧₂ {`𝟚} {`𝟚} (`!r p) = {!!}
⟦_⟧₂ {`𝟚} {`𝟚} (`assoc p q r) = {!!}
