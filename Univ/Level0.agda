{-# OPTIONS --type-in-type --without-K #-}

module Univ.Level0 where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function renaming (_∘_ to _○_)
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_)

open import Univ.Universe

infix 50 _⊕_
infix 60 _⊗_

data U : Set where
  𝟘 𝟙 : U
  _⊕_ _⊗_ : U → U → U

El : U → Set
El 𝟘       = ⊥
El 𝟙       = ⊤
El (A ⊕ B) = El A ⊎ El B
El (A ⊗ B) = El A × El B

Fun : (A B : U) → Set
Fun A B = El A → El B

_∼_ : {A B : U} → (f g : Fun A B) → Set
_∼_ {A} {B} f g = (a : El A) → f a == g a

refl∼ : {A B : U} → (f : Fun A B) → (f ∼ f)
refl∼ f a = refl

sym∼ : {A B : U} {f g : Fun A B} → (f ∼ g) → (g ∼ f)
sym∼ H b = sym (H b)

trans∼ : {A B : U} {f g h : Fun A B} → f ∼ g → g ∼ h → f ∼ h
trans∼ p₁ p₂ a = trans (p₁ a) (p₂ a)

∼○ : {A B C : U} {f g : Fun A B} {h k : Fun B C} →
     (f ∼ g) → (h ∼ k) → ((h ○ f) ∼ (k ○ g))
∼○ {f = f} {g = g} {h = h} H₁ H₂ x = trans (cong h (H₁ x)) (H₂ (g x))

record isequiv {A B : U} (f : Fun A B) : Set where
  constructor mkisequiv
  field
    g : El B → El A
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

_≃_ : (A B : U) → Set
A ≃ B = Σ (Fun A B) isequiv

id≃ : {A : U} → A ≃ A
id≃ = (id , mkisequiv id (λ a → refl) (λ a → refl))

sym≃ : {A B : U} → A ≃ B → B ≃ A
sym≃ (f , mkisequiv g α β) = (g , mkisequiv f β α)

trans≃ : {A B C : U} → A ≃ B → B ≃ C → A ≃ C
trans≃ {A} {B} {C} (f , mkisequiv f⁻ α₁ β₁) (g , mkisequiv g⁻ α₂ β₂) =
  g ○ f , mkisequiv (f⁻ ○ g⁻) α β
    where α : (x : El C) → (g (f (f⁻ (g⁻ x)))) == x
          α x = trans (cong g (α₁ (g⁻ x))) (α₂ x)
          β : (x : El A) → (f⁻ (g⁻ (g (f x)))) == x
          β x = trans (cong f⁻ (β₂ (f x))) (β₁ x)

A⊎⊥≃A : {A : U} → A ⊕ 𝟘 ≃ A
A⊎⊥≃A {A} = f , mkisequiv g (λ a → refl) β
  where
    f : (El A ⊎ ⊥) → El A
    f (inj₁ a) = a
    f (inj₂ ())

    g : El A → (El A ⊎ ⊥)
    g a = inj₁ a

    β : (g ○ f) ∼ id
    β (inj₁ a) = refl
    β (inj₂ ())

postulate
  funext : Extensionality _ _

Univ0 : Universe
Univ0 = record
            { U = U
            ; El = El
            ; Fun = Fun
            ; _∼_ = _∼_
            ; _≡_ = _==_
            ; _≃_ = _≃_
            ; SynCat = record
                         { id = id
                         ; _∘_ = λ g f → g ○ f
                         ; assoc = λ _ → refl
                         ; identityˡ = λ _ → refl
                         ; identityʳ = λ _ → refl
                         ; equiv = record { refl = λ _ → refl
                                          ; sym = λ x a → sym (x a)
                                          ; trans = λ x y a → trans (x a) (y a) }
                         ; ∘-resp-≡ = λ {_} {_} {_} {f} {g} {h} {i} x y a → trans (cong f (y a)) (x (i a)) }
            ; ElFunc = record { F = id
                              ; identity = refl
                              ; homomorphism = refl
                              ; F-resp-≡ = funext }
            }
