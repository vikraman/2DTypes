module PiFin.NatEx where

open import IntensionalTypeTheory

data _≤_ : ℕ → ℕ → Type₀ where
  z≤n : ∀ {n} → zero ≤ n
  s≤n : ∀ {m n} → m ≤ n → succ m ≤ succ n

≤-refl : ∀ n → n ≤ n
≤-refl zero = z≤n
≤-refl (succ n) = s≤n (≤-refl n)

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans {zero} z≤n q = z≤n
≤-trans {succ m} (s≤n p) (s≤n q) = s≤n (≤-trans p q)

≤-succ : ∀ m → m ≤ succ m
≤-succ zero = z≤n
≤-succ (succ n) = s≤n (≤-succ n)

_<_ : ℕ → ℕ → Type₀
m < n = succ m ≤ n

_>_ : ℕ → ℕ → Type₀
m > n = n < m

open import PiFin.Dec

_≤?_ : Decidable _≤_
zero ≤? n = yes z≤n
succ m ≤? zero = no (λ ())
succ m ≤? succ n with m ≤? n
... | yes m≤n = yes (s≤n m≤n)
... | no  m≰n = no (m≰n ∘ (λ { (s≤n m≤n) → m≤n }))

compare : ∀ m n → (m < n) + (m == n) + (m > n)
compare zero zero = i₂ (i₁ (refl zero))
compare zero (succ n) = i₁ (s≤n z≤n)
compare (succ m) zero = i₂ (i₂ (s≤n z≤n))
compare (succ m) (succ n) with compare m n
... | i₁ m<n = i₁ (s≤n m<n)
... | i₂ (i₁ m=n) = i₂ (i₁ (ap succ m=n))
... | i₂ (i₂ n>m) = i₂ (i₂ (s≤n n>m))
