{-# OPTIONS --without-K #-}

module B2 where

open import Function
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
-- open import Equiv

record IsEquiv {A B : Set} (f : A → B) : Set where
  constructor isequiv
  field
    g : B → A
    α : ∀ a → g (f a) ≡ a
    β : ∀ b → f (g b) ≡ b

Equiv : (A B : Set) → Set
Equiv A B = Σ[ f ∈ (A → B) ] IsEquiv f

syntax Equiv A B = A ≃ B

record IsEqEquiv {A B : Set} (p q : A ≃ B) : Set where
  constructor iseqequiv
  fp = proj₁ p
  fq = proj₁ q
  open IsEquiv (proj₂ p) renaming (g to gp ; α to αp ; β to βp)
  open IsEquiv (proj₂ q) renaming (g to gq ; α to αq ; β to βq)
  field
    f : (a : A) → fp a ≡ fq a
    g : (b : B) → gp b ≡ gq b

syntax IsEqEquiv p q = p ≅ q

data U : Set where
  `Bool : U

El : U → Set
El `Bool = Bool

data ⊢_ : U → Set where
  `false `true : ⊢ `Bool

El⊢ : {A : U} → ⊢ A → El A
El⊢ `false = false
El⊢ `true = true

El⊣ : {A : U} → El A → ⊢ A
El⊣ {`Bool} false = `false
El⊣ {`Bool} true = `true

data _==_ : U → U → Set where
  idp notp : `Bool == `Bool

eval : {A B : U} → (p : A == B) → ⊢ A → ⊢ B
eval idp  `false = `false
eval idp  `true  = `true
eval notp `false = `true
eval notp `true  = `false

El-eval : {A B : U} → (p : A == B) → El A → El B
El-eval p a = El⊢ (eval p (El⊣ a))

El== : {A B : U} → A == B → El A ≃ El B
El== idp =
  id , isequiv id
  (λ { false → refl ; true → refl })
  (λ { false → refl ; true → refl })
El== notp =
  not , isequiv not
  (λ { false → refl ; true → refl })
  (λ { false → refl ; true → refl })

data _===_ {A B : U} : (p q : A == B) → Set where
  idpp : (p : A == B) → p === p

El=== : {A B : U} {p q : A == B} → (p === q) → El== p ≅ El== q
El=== (idpp idp) =
  iseqequiv (λ { false → refl ; true → refl })
            (λ { false → refl ; true → refl })
El=== (idpp notp) =
  iseqequiv (λ { false → refl ; true → refl })
            (λ { false → refl ; true → refl })

idtoequiv = El==

ua : {A B : U} → El A ≃ El B → A == B
ua {`Bool} {`Bool} (f , isequiv g α β) with f false
... | false = idp
... | true = notp

α-eq : {A B : U} (eq : El A ≃ El B) → idtoequiv (ua eq) ≅ eq
α-eq {`Bool} {`Bool} (f , isequiv g α β) with f false
... | false = iseqequiv (λ { false → {!!} ; true → {!!} })
                        (λ { false → {!!} ; true → {!!} })
... | true  = iseqequiv (λ { false → {!!} ; true → {!!} })
                        (λ { false → {!!} ; true → {!!} })

β-eq : {A B : U} (p : A == B) → ua (idtoequiv p) ≡ p
β-eq {`Bool} {`Bool} idp = refl
β-eq {`Bool} {`Bool} notp = refl

univalence : {A B : U} → (A == B) ≃ (El A ≃ El B)
univalence = idtoequiv , isequiv ua β-eq {!!}

module _ (funext : {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g) where

  β== : {A B : U} → (p : A == B) → proj₁ (idtoequiv p) ≡ El-eval p
  β== idp = funext (λ { false → refl ; true → refl })
  β== notp = funext (λ { false → refl ; true → refl })
