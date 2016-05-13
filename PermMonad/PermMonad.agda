{-# OPTIONS --without-K #-}

module PermMonad where
open import Categories.Category
open import Categories.Groupoid
open import Categories.Monad
open import Categories.Support.PropositionalEquality
open import Categories.Support.Equivalence
open import Categories.Support.EqReasoning

open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat
open import Data.Unit
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_+_ to _ℤ+_)
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Algebra.FunctionProperties
import Relation.Binary.PropositionalEquality as P
open P.≡-Reasoning
open Algebra.FunctionProperties (P._≡_ {A = ℤ})
open import Relation.Binary
  using (Rel; IsEquivalence; module IsEquivalence; Reflexive; Symmetric; Transitive)
  renaming (_⇒_ to _⊆_)

open import Comonad
open import PermPi

F₁≡ : {τ : U} {p : τ ⟷ τ} {A B : Category.Obj (p!p⇒C p)} (k : ℕ)
    → ap (compose k (! p)) A ≣ B
    → ap (compose k (! p)) (ap p A) ≣ ap p B
F₁≡ {τ} {p} {A} {B} ℕ.zero eq = ≣-cong (ap p) eq
F₁≡ {τ} {p} {A} {B} (ℕ.suc k) eq =
       ap (compose k (! p)) (ap (! p) (ap p A))
    ≡⟨ ≣-cong (ap (compose k (! p))) (ap!≡ {p = p} P.refl) ⟩
       ap (compose k (! p)) A
    ≡⟨ ≣-sym (ap≡ {p = p} P.refl) ⟩
       ap p (ap (! p) (ap (compose k (! p)) A))
    ≡⟨ ≣-cong (ap p) (≣-sym (compose≡ {p = ! p} k 1 P.refl P.refl)) ⟩
       ap p (ap (compose (k + 1) (! p)) A)
    ≡⟨ ≣-cong (λ n → ap p (ap (compose n (! p)) A)) (+-comm k 1) ⟩
       ap p (ap (compose (1 + k) (! p)) A)
    ≡⟨ ≣-cong (ap p) (compose≡ {p = ! p} 1 k P.refl P.refl) ⟩
       ap p (ap (compose k (! p)) (ap (! p) A))
    ≡⟨ ≣-cong (ap p) eq ⟩
       ap p B ∎

coF₁≡ : {τ : U} {p : τ ⟷ τ} {A B : Category.Obj (p!p⇒C p)} (k : ℕ)
      → ap (compose k p) B ≣ A
      → ap (compose k p) (ap (! p) B) ≣ ap (! p) A
coF₁≡ {τ} {p} {A} {B} ℕ.zero eq    = ≣-cong (ap (! p)) eq
coF₁≡ {τ} {p} {A} {B} (ℕ.suc k) eq =
      ap (compose k p) (ap p (ap (! p) B))
   ≡⟨ ≣-cong (ap (compose k p)) (ap≡ {p = p} P.refl) ⟩
      ap (compose k p) B
   ≡⟨ ≣-sym (ap!≡ {p = p} P.refl) ⟩
      ap (! p) (ap p (ap (compose k p) B))
   ≡⟨ ≣-cong (ap (! p)) (≣-sym (compose≡ {p = p} k 1 P.refl P.refl)) ⟩
      ap (! p) (ap (compose (k + 1) p) B)
   ≡⟨ ≣-cong (λ n → ap (! p) (ap (compose n p) B)) (+-comm k 1) ⟩
      ap (! p) (ap (compose (1 + k) p) B)
   ≡⟨ ≣-cong (ap (! p)) (compose≡ {p = p} 1 k P.refl P.refl) ⟩
      ap (! p) (ap (compose k p) (ap p B))
   ≡⟨ ≣-cong (ap (! p)) eq ⟩
      ap (! p) A ∎

-- need order of permutation
postulate
  ord : {τ : U} (p : τ ⟷ τ) → Σ[ k ∈ ℕ ] (compose k p) ≡ ! p

ordid⟷ : {τ : U} {p : τ ⟷ τ} {X : ⟦ τ ⟧} (n : ℕ)
         → (compose n p) ≡ (! p)
         → ap (compose (ℕ.suc n) p) X ≡ ap id⟷ X
ordid⟷ {τ} {p} {X }n eqn = ap (compose (ℕ.suc n) p) X
                          ≡⟨ ≣-refl ⟩
                             ap (p ◎ compose n p) X
                          ≡⟨ ≣-cong (λ q → ap (p ◎ q) X) eqn ⟩
                             ap (p ◎ ! p) X
                          ≡⟨ ap∼ (linv◎l {c = p}) ⟩
                             ap id⟷ X ∎

ord≡' : {τ : U} {p : τ ⟷ τ} {X : ⟦ τ ⟧} (n : ℕ)
      → ap (compose (ℕ.suc n) p) (ap (compose n (! p)) X) ≡ ap p X
ord≡' {τ} {p} {X} ℕ.zero    = ≣-refl
ord≡' {τ} {p} {X} (ℕ.suc n) =  ap (compose n p) (ap p (ap p (ap (compose n (! p)) (ap (! p) X))))
                            ≡⟨ ap∼ (composeAssoc n) ⟩
                               ap p (ap (compose (ℕ.suc n) p) (ap (compose n (! p)) (ap (! p) X)))
                            ≡⟨ P.cong (ap p) (ord≡' n) ⟩
                               ap p (ap p (ap (! p) X))
                            ≡⟨ ≣-cong (ap p) (ap≡ {p = p} P.refl) ⟩
                               ap p X ∎

ord≡ : {τ : U} {p : τ ⟷ τ} {X : ⟦ τ ⟧} (n : ℕ)
     → (compose n p) ≡ (! p)
     → ap (compose n (! p)) X ≣ ap p X
ord≡ {τ} {p} {X} n eqn =  ap (compose n (! p)) X
                       ≡⟨ ≣-refl ⟩
                          ap id⟷ (ap (compose n (! p)) X)
                       ≡⟨ ≣-sym (ordid⟷ n eqn) ⟩
                          ap (compose (ℕ.suc n) p) (ap (compose n (! p)) X)
                       ≡⟨ ord≡' n ⟩
                          ap p X ∎

η⇒ : {τ : U} {p : τ ⟷ τ} {X : ⟦ τ ⟧}
   → Σ[ k ∈ ℕ ] (compose k p) ≡ ! p
   → Σ[ k ∈ ℕ ] (ap (compose k (! p)) X ≣ ap p X)
η⇒ {τ} {p} {X} (n  , eqn) = n , ord≡ n eqn

μ⇒ : {τ : U} {p : τ ⟷ τ} {X : ⟦ τ ⟧} (n : ℕ)
   → (compose n p) ≡ ! p
   → (ap (compose n p) (ap p (ap p X)) ≡ ap p X)
μ⇒ {τ} {p} {X} n eqn =  ap (compose n p) (ap p (ap p X))
                     ≡⟨ P.cong (λ q → ap q (ap p (ap p X))) eqn ⟩
                        ap (! p) (ap p (ap p X))
                     ≡⟨ ap!≡ {p = p} ≣-refl ⟩
                        ap p X ∎

PermMonad : {τ : U} (p : τ ⟷ τ) → Monad (p!p⇒C p)
PermMonad {τ} p with (ord p)
PermMonad {τ} p | (n , eqn) =
          record { F = record { F₀ = ap p
                              ; F₁ = λ {((k , eq) , (k⁻¹ , eq⁻¹))
                                     → (k   , ≣-trans (ap∼ (composeAssoc k))
                                                      (≣-cong (λ x → ap p x) eq))
                                     , (k⁻¹ , F₁≡ k⁻¹ eq⁻¹)} }
                 ; η = record { η = λ X → (1 , ≣-refl)
                                        , η⇒ (n , eqn)
                 ; commute = λ _ → tt }
                 ; μ = record { η = λ X → (n , μ⇒ n eqn)
                                        , (1 , (ap!≡ {p = p} P.refl))
                              ; commute = λ _ → tt }
                 ; assoc = tt
                 ; identityˡ = tt
                 ; identityʳ = tt}

PermComonad : {τ : U} (p : τ ⟷ τ) → Comonad (p!p⇒C p)
PermComonad {τ} p with (ord p)
PermComonad {τ} p | (n , eqn) =
            record { F = record { F₀ = ap (! p)
                                ; F₁ = λ {((k , eq) , (k⁻¹ , eq⁻¹))
                                       → (k   , coF₁≡ k eq)
                                       , (k⁻¹ , ≣-trans (ap∼ (composeAssoc k⁻¹))
                                                        (≣-cong (ap (! p)) eq⁻¹)) }}
                   ; η = record { η = λ X → (1 , (ap∼ (rinv◎l {c = p})))
                                          , (n , ≣-trans (ord≡ n eqn)
                                                         (ap∼ (rinv◎l {c = p})))
                                ; commute = λ _ → tt }
                   ; μ = record { η = λ X → (n , ≣-cong (λ q → ap q (ap (! p) X)) eqn)
                                          , (1 , ≣-refl)
                                ; commute = λ _ → tt }
                   ; assoc = tt
                   ; identityˡ = tt
                   ; identityʳ = tt}
