module TruncationExamples where

open import Type
open import One
open import Two
open import NaturalNumbers
open import DependentSum
open import Equivalences
open import Paths
open import PathsInSigma
open import Univalence
open import PropositionalTruncation

-- A few examples to gain some intuition about propositional truncation

-- Truncated Bool is One

∣𝟚∣≡𝟙 :  ∥ 𝟚 ∥ == 𝟙
∣𝟚∣≡𝟙 = ua ((λ _ → 0₁) ,
            qinv-is-equiv ((λ _ → ∣ 0₂ ∣) ,
                           (λ x → identify _ _) ,
                           (λ { 0₁ → refl 0₁ })))

-- Truncated existential ∃ x. x ≤ 3

data _≤_ : ℕ → ℕ → Type₀ where
  z≤n : ∀ {n}                 → 0  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → succ m ≤ succ n

x y z w : Σ ℕ (λ n → n ≤ 3)
x = (0 , z≤n)
y = (1 , s≤s z≤n)
z = (2 , s≤s (s≤s z≤n))
w = (3 , s≤s (s≤s (s≤s z≤n)))

-- It is definitely not the case that ∥ n ≤ 3 ∥ == One for all n. But if we
-- truncate, we get:

Σ== : ∥ Σ ℕ (λ n → n ≤ 3) ∥ == 𝟙
Σ== = ua ((λ _ → 0₁) ,
          qinv-is-equiv ((λ _ → ∣ (0 , z≤n) ∣) ,
                         (λ x → identify _ _) ,
                         (λ { 0₁ → refl 0₁ })))
