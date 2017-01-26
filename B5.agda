{-# OPTIONS --without-K #-}

module B5 where

open import Level
open import Function
open import Data.Bool
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Equiv

record Ell {u e} (U : Set u) (E : Set e) : Set (u ⊔ e) where
  field
    El : U → E

syntax Ell U E = ⟦ U ⟧= E

data U : Set where
  `Bool : U

El : U → Set
El `Bool = Bool

⟦U⟧ : ⟦ U ⟧= Set
⟦U⟧ =
  record {
    El = El
  }

Fib : U → Set
Fib A = El A → U

Π : (A : U) → Fib A → Set
Π A B = (x : El A) → El (B x)

_⟶_ : U → U → Set
A ⟶ B = Π A (λ _ → B)

data _⟷_ : U → U → Set where
  `id `not : `Bool ⟷ `Bool

⟦⟷⟧ : (A B : U) → ⟦ A ⟷ B ⟧= (El A ≃ El B)
⟦⟷⟧ `Bool `Bool =
  record {
    El = λ { `id → qeq id id (λ { false → refl ; true → refl })
                             (λ { false → refl ; true → refl })
           ; `not → qeq not not (λ { false → refl ; true → refl })
                                (λ { false → refl ; true → refl })
           }
  }

idp : (A : U) → A ⟷ A
idp `Bool = `id

module _ {C : {A B : U} → A ⟷ B → U} (c : {A : U} → El (C (idp A))) where

  private
    lemma : {A' B' : U} (p : A' ⟷ B') → C p ≡ `Bool
    lemma `id with C `id
    ... | `Bool = refl
    lemma `not with C `not
    ... | `Bool = refl

  J : {A B : U} → (p : A ⟷ B) → El (C p)
  J `id = case subst El (lemma `id) c of
            (λ { false → subst El (sym (lemma `id)) false
               ; true  → subst El (sym (lemma `id)) true })
  J `not = case subst El (lemma `id) c of
            (λ { false → subst El (sym (lemma `not)) true
               ; true  → subst El (sym (lemma `not)) false })

  J-β : J `id ≡ c
  J-β with (subst El (lemma `id)) c | inspect (subst El (lemma `id)) c
  ... | false | [ eq ] = {!!}
  ... | true  | [ eq ] = {!!}
