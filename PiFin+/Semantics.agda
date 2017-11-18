{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module PiFin+.Semantics where

open import HoTT
  using (Type; Type₀; Type₁; lsucc; lmax;
         of-type; -- syntax u :> A
         _∘_; is-inj;
         ⊥; ⊥-elim;
         ⊤; unit;
         ℕ; O; S;
         _⊔_; inl; inr;
         Σ; _,_ ; fst; snd; pair=; fst=;
         Ptd; ⊙[_,_]; pt;
         Trunc; [_]; Trunc-elim; Trunc=-equiv;
         _==_; idp; !; ap; ua; coe; coe-equiv;
         PathOver; -- syntax u == v [ B ↓ p ]
         _≃_; is-equiv; is-eq; equiv; transport-equiv; –>; <–;
         has-level-in; is-contr; is-prop; is-connected;
         inhab-prop-is-contr; prop-has-all-paths; prop-has-all-paths-↓
         )

-- Every finite type in Π can be represented by a natural number. We embed this
-- natural into the HoTT universe

El : ℕ → Type₀
El O = ⊥
El (S n) = ⊤ ⊔ El n

-- A path between ⊤ ⊔ X and ⊤ ⊔ Y induces a path between X and Y
-- Proof is tedious combinatorics

⊤-cncl : ∀ {ℓ} {X Y : Type ℓ} → ⊤ ⊔ X == ⊤ ⊔ Y → X == Y
⊤-cncl = ua ∘ ⊤-cncl≃ ∘ coe-equiv
  where
    reduce-aux : ∀ {ℓ} {X Y : Type ℓ} →
                 {x : X} → {f : ⊤ ⊔ X → ⊤ ⊔ Y} → {g : ⊤ ⊔ Y → ⊤ ⊔ X} →
                 (f-g : (y : ⊤ ⊔ Y) → f (g y) == y) →
                 Σ (⊤ ⊔ Y) (λ y → f (inl unit) == y) →
                 Σ (⊤ ⊔ Y) (λ y → f (inr x) == y) →
                 Y
    reduce-aux f-g (inl unit , p) (inl unit , q) = {!!}
    reduce-aux f-g (inl unit , p) (inr y , q)    = y
    reduce-aux f-g (inr y , p)    (inl unit , q) = y
    reduce-aux f-g (inr y , p)    (inr y' , q)   = y'

    reduce : ∀ {ℓ} {X Y : Type ℓ} →
             (f : ⊤ ⊔ X → ⊤ ⊔ Y) → (g : ⊤ ⊔ Y → ⊤ ⊔ X) →
             (f-g : (y : ⊤ ⊔ Y) → f (g y) == y) → X → Y
    reduce f g f-g x =
      reduce-aux {x = x} {f = f} {g = g}
        f-g (f (inl unit) , idp) (f (inr x) , idp)

    reduce-η : ∀ {ℓ} {X Y : Type ℓ} →
               (f : ⊤ ⊔ X → ⊤ ⊔ Y) → (g : ⊤ ⊔ Y → ⊤ ⊔ X) →
               (f-g : (y : ⊤ ⊔ Y) → f (g y) == y) →
               (g-f : (x : ⊤ ⊔ X) → g (f x) == x) →
               (x : X) → reduce g f g-f (reduce f g f-g x) == x
    reduce-η = {!!}

    ⊤-cncl≃ : ∀ {ℓ} {X Y : Type ℓ} → (⊤ ⊔ X ≃ ⊤ ⊔ Y) → (X ≃ Y)
    ⊤-cncl≃ (f , record { g = g ; f-g = f-g ; g-f = g-f ; adj = adj }) =
      reduce f g f-g ,
      is-eq
        _
        (reduce g f g-f)
        (reduce-η g f g-f f-g)
        (reduce-η f g f-g g-f)

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
