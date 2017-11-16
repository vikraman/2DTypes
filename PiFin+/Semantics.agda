{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module PiFin+.Semantics where

open import HoTT

El : ℕ → Type₀
El O = ⊥
El (S n) = ⊤ ⊔ El n

is-finite : Type₀ → Type₁
is-finite X = Σ ℕ λ n → Trunc -1 (El n == X)

-- port over from EmbeddingsInUniverse
is-finite-path : (X : Type₀) → (φ₁ φ₂ : is-finite X) → φ₁ == φ₂
is-finite-path X (O , ψ₁) (O , ψ₂) = pair= idp (prop-has-all-paths ψ₁ ψ₂)
is-finite-path X (O , ψ₁) (S m , ψ₂) = {!!}
is-finite-path X (S n , ψ₁) (O , ψ₂) = {!!}
is-finite-path X (S n , ψ₁) (S m , ψ₂) = pair= (ap S {!!}) {!!}

is-finite-is-prop : (X : Type₀) → is-prop (is-finite X)
is-finite-is-prop X = has-level-in p
  where p : (φ₁ φ₂ : is-finite X) → is-contr (φ₁ == φ₂)
        p φ₁ φ₂ = inhab-prop-is-contr (is-finite-path X φ₁ φ₂) {{{!!}}}

M : Type₁
M = Σ Type₀ is-finite

BAut : ∀ {ℓ} → Type ℓ → Type (lsucc ℓ)
BAut {ℓ} T = Σ (Type ℓ) λ X → Trunc -1 (T == X)

⊙BAut : ∀ {ℓ} → Type ℓ → Ptd (lsucc ℓ)
⊙BAut T = ⊙[ BAut T , (T , [ idp ]) ]

BAut-trunc-path : ∀ {ℓ} (T X : Type ℓ) (φ : Trunc -1 (T == X))
                → Trunc -1 ((T , [ idp ]) == (X , φ) :> BAut T)
BAut-trunc-path {ℓ} T X = Trunc-elim λ p → [ pair= p prop-has-all-paths-↓ ]

BAut-0-conn : ∀ {ℓ} (T : Type ℓ) → is-connected 0 (BAut T)
BAut-0-conn T = has-level-in ( [ pt (⊙BAut T) ]
                             , Trunc-elim λ { (X , φ) → <– (Trunc=-equiv [ T , [ idp ] ] [ X , φ ])
                                                           (BAut-trunc-path T X φ) } )

N : Type₁
N = Σ ℕ λ n → BAut (El n)

M≃N : M ≃ N
M≃N = equiv f g f-g g-f
  where f : M → N
        f (T , n , φ) = n , T , φ
        g : N → M
        g (n , T , φ) = (T , n , φ)
        f-g : (b : N) → f (g b) == b
        f-g (n , T , φ) = idp
        g-f : (a : M) → g (f a) == a
        g-f (T , n , φ) = idp

paths-in-M : {X Y : M} → X == Y → fst (snd X) == fst (snd Y)
paths-in-M idp = idp

paths-in-N : {X Y : N} → X == Y → fst X == fst Y
paths-in-N idp = idp

BAut= : ∀ {ℓ} {X Y : Type ℓ} → X == Y → BAut X == BAut Y
BAut= = ap BAut

BAut∘El= : ∀ {m n : ℕ} → m == n → BAut (El m) == BAut (El n)
BAut∘El= = ap (BAut ∘ El)

N-in : ∀ {m n : ℕ} → (p : m == n) → pt (⊙BAut (El m)) == pt (⊙BAut (El n)) [ BAut ∘ El ↓ p ]
N-in idp = idp

is-univ-fib : ∀ {i j} {A : Type i} (B : A → Type j) → Type (lmax i j)
is-univ-fib B = ∀ {x y} → is-equiv (transport-equiv B {x} {y})

pred-ext-is-univ : ∀ {i j} → (B : Type i → Type j) → (φ : (X : Type i) → is-prop (B X))
                 → is-univ-fib (fst {B = B})
pred-ext-is-univ B φ = {!!}

finite-types-is-univ : is-univ-fib (fst {A = Type₀} {is-finite})
finite-types-is-univ = {!!}
