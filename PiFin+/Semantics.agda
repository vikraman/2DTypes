{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module PiFin+.Semantics where

open import HoTT

El : ℕ → Type₀
El O = ⊥
El (S n) = ⊤ ⊔ El n

-- port over from EmbeddingsInUniverse
⊤-cncl : ∀ {ℓ} {X Y : Type ℓ} → ⊤ ⊔ X == ⊤ ⊔ Y → X == Y
⊤-cncl = {!!}

El-is-inj : is-inj El
El-is-inj O O p = idp
El-is-inj O (S n) p = ⊥-elim (coe (! p) (inl unit))
El-is-inj (S m) O p = ⊥-elim (coe p (inl unit))
El-is-inj (S m) (S n) p = ap S (El-is-inj m n (⊤-cncl p))

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

M₀ : ℕ → M
M₀ n = El n , n , [ idp ]

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

M=N : M == N
M=N = ua M≃N

paths-in-M : {X Y : M} → X == Y → fst (snd X) == fst (snd Y)
paths-in-M idp = idp

paths-in-N : {X Y : N} → X == Y → fst X == fst Y
paths-in-N idp = idp

M→N= : {X Y : M} → X == Y → –> M≃N X == –> M≃N Y
M→N= p = ap (–> M≃N) p

BAut= : ∀ {ℓ} {X Y : Type ℓ} → X == Y → BAut X == BAut Y
BAut= = ap BAut

BAut∘El= : ∀ {m n : ℕ} → m == n → BAut (El m) == BAut (El n)
BAut∘El= = ap (BAut ∘ El)

↓-BAut-El-in : ∀ {m n : ℕ} → (p : m == n) → pt (⊙BAut (El m)) == pt (⊙BAut (El n)) [ BAut ∘ El ↓ p ]
↓-BAut-El-in idp = idp

N-in : {m n : ℕ} → m == n → (m , pt (⊙BAut (El m))) == (n , pt (⊙BAut (El n)))
N-in p = pair= p (↓-BAut-El-in p)

M₀= : {m n : ℕ} → m == n → M₀ m == M₀ n
M₀= = ap M₀

M₀=-out : {m n : ℕ} → M₀ m == M₀ n → m == n
M₀=-out {m} {n} p = El-is-inj m n (fst= p)

is-univ-fib : ∀ {i j} {A : Type i} (B : A → Type j) → Type (lmax i j)
is-univ-fib B = ∀ {x y} → is-equiv (transport-equiv B {x} {y})

pred-ext-is-univ : ∀ {i j} → (B : Type i → Type j) → (φ : (X : Type i) → is-prop (B X))
                 → is-univ-fib (fst {B = B})
pred-ext-is-univ B φ = {!!}

finite-types-is-univ : is-univ-fib (fst {A = Type₀} {is-finite})
finite-types-is-univ = {!!}
