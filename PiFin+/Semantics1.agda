{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module PiFin+.Semantics1 where

open import HoTT
open import PiFin+.Semantics0

-----------------------------------------------------------------------------
--
-- Every finite type in Π can be represented by a natural number. We embed this
-- natural into the HoTT universe

El : ℕ → Type₀
El O = ⊥
El (S n) = ⊤ ⊔ El n

El-is-inj : is-inj El
El-is-inj O O p = idp
El-is-inj O (S n) p = ⊥-elim (coe (! p) (inl unit))
El-is-inj (S m) O p = ⊥-elim (coe p (inl unit))
El-is-inj (S m) (S n) p = ap S (El-is-inj m n (⊤-cncl p))

is-finite : Type₀ → Type₁
is-finite X = Σ ℕ λ n → Trunc -1 (El n == X)

instance
  is-finite-is-prop : {X : Type₀} → is-prop (is-finite X)
  is-finite-is-prop {X} = all-paths-is-prop is-finite-path
    where
      -- instance search failing
      is-finite-path : (φ₁ φ₂ : is-finite X) → φ₁ == φ₂
      is-finite-path (O , ψ₁) (O , ψ₂) =
        pair= idp (prop-has-all-paths ψ₁ ψ₂)
      is-finite-path (O , ψ₁) (S m , ψ₂) =
        ⊥-elim (Trunc-elim (λ p → coe p (inl tt))
                           (Trunc-fmap2 _∙_ ψ₂ (Trunc-fmap ! ψ₁)))
      is-finite-path (S n , ψ₁) (O , ψ₂) =
        ⊥-elim (Trunc-elim (λ p → coe p (inl tt))
                           (Trunc-fmap2 _∙_ ψ₁ (Trunc-fmap ! ψ₂)))
      is-finite-path (S n , ψ₁) (S m , ψ₂) =
        pair= (Trunc-elim (λ p → ap S (El-is-inj n m (⊤-cncl p)))
                          (Trunc-fmap2 _∙_ ψ₁ (Trunc-fmap ! ψ₂)))
              prop-has-all-paths-↓

M : Type₁
M = Σ Type₀ is-finite

M₀ : ℕ → M
M₀ n = El n , n , [ idp ]

-- BAut : ∀ {ℓ} → Type ℓ → Type (lsucc ℓ)
-- BAut {ℓ} T = Σ (Type ℓ) λ X → Trunc -1 (T == X)

⊙BAut : ∀ {ℓ} → Type ℓ → Ptd (lsucc ℓ)
⊙BAut T = ⊙[ BAut T , (T , [ idp ]) ]

-- BAut-trunc-path : ∀ {ℓ} (T X : Type ℓ) (φ : Trunc -1 (T == X))
--                 → Trunc -1 ((T , [ idp ]) == (X , φ) :> BAut T)
-- BAut-trunc-path {ℓ} T X = Trunc-elim λ p → [ pair= p prop-has-all-paths-↓ ]

BAut-0-conn : ∀ {ℓ} (T : Type ℓ) → is-connected 0 (BAut T)
BAut-0-conn T = has-level-in ( [ pt (⊙BAut T) ]
                             , Trunc-elim λ { (X , φ) → <– (=ₜ-equiv [ T , [ idp ] ] [ X , φ ])
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

BAut-SubtypeProp : ∀ {ℓ} → (T : Type ℓ) → SubtypeProp (Type ℓ) (lsucc ℓ)
BAut-SubtypeProp T = (λ X → Trunc -1 (T == X)) , (λ _ → Trunc-level)

BAut-level : ∀ {ℓ} {n : ℕ₋₂} {T : Type ℓ} {{φ : has-level n T}} → (X : BAut T) → has-level n (fst X)
BAut-level {n = n} {{φ}} (X , ψ) = Trunc-elim (λ p → transport (has-level n) p φ) ψ

BAut= : ∀ {ℓ} {T : Type ℓ} (X Y : BAut T) → Type (lsucc ℓ)
BAut= {T = T} = Subtype= (BAut-SubtypeProp T)

BAut=-econv : ∀ {ℓ} {T : Type ℓ} (X Y : BAut T) → (BAut= X Y) ≃ (X == Y)
BAut=-econv {T = T} = Subtype=-econv (BAut-SubtypeProp T)

_-BAut-level : ∀ {ℓ} (n : ℕ₋₂) {T : Type ℓ} {{φ : has-level n T}} → has-level (S n) (BAut T)
_-BAut-level n {{φ}} =
  has-level-in λ { X Y → equiv-preserves-level (BAut=-econv X Y)
                         {{universe-=-level (BAut-level X) (BAut-level Y)}} }

instance
  BAut-prop-is-set : ∀ {ℓ} {T : Type ℓ} → {{φ : is-prop T}} → is-set (BAut T)
  BAut-prop-is-set = S ⟨-2⟩ -BAut-level

  BAut-set-is-gpd : ∀ {ℓ} {T : Type ℓ} → {{φ : is-set T}} → is-gpd (BAut T)
  BAut-set-is-gpd = S (S ⟨-2⟩) -BAut-level

  El-is-set : {n : ℕ} → is-set (El n)
  El-is-set {O} = has-level-in (λ ())
  El-is-set {S n} = ⊔-level ⟨⟩ (El-is-set {n})

-- stronger than being a set
El-has-dec-eq : {n : ℕ} → has-dec-eq (El n)
El-has-dec-eq {O} X Y = inr (λ _ → X)
El-has-dec-eq {S n} (inl unit) (inl unit) = inl idp
El-has-dec-eq {S n} (inl unit) (inr Y) = inr (λ ())
El-has-dec-eq {S n} (inr X) (inl unit) = inr (λ ())
El-has-dec-eq {S n} (inr X) (inr Y) = f (El-has-dec-eq X Y)
  where f : Dec (X == Y) → Dec (inr X == inr Y)
        f (inl  p) = inl (ap inr p)
        f (inr ¬p) = inr (λ q → ¬p (–> (inr=inr-equiv X Y) q))

-- alternative proof using hedberg's lemma
El-is-set' : {n : ℕ} → is-set (El n)
El-is-set' = dec-eq-is-set El-has-dec-eq

N-is-gpd : is-gpd N
N-is-gpd = ⟨⟩ ⟨⟩

M-is-gpd : is-gpd M
M-is-gpd = equiv-preserves-level (M≃N ⁻¹)

paths-in-M : {X Y : M} → X == Y → fst (snd X) == fst (snd Y)
paths-in-M idp = idp

paths-in-N : {X Y : N} → X == Y → fst X == fst Y
paths-in-N idp = idp

M→N= : {X Y : M} → X == Y → –> M≃N X == –> M≃N Y
M→N= p = ap (–> M≃N) p

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

tpt-eqv-fst : ∀ {i j} {P : Type i → Type j} {X Y : Type i} → (p : X == Y)
            → {ux : P X} {uy : P Y} → (up : ux == uy [ P ↓ p ])
            → transport-equiv fst (pair= p up) == coe-equiv p
tpt-eqv-fst idp idp = idp

Subtype-is-univ : ∀ {i j} (P : SubtypeProp (Type i) j) → is-univ-fib (fst {A = Type i} {B = fst P})
Subtype-is-univ P {X , φ₁} {Y , φ₂} = is-eq f g f-g g-f
  where f : X , φ₁ == Y , φ₂ → X ≃ Y
        f = transport-equiv fst
        g : X ≃ Y → X , φ₁ == Y , φ₂
        g e = Subtype=-out P (ua e)
        f-g : (b : X ≃ Y) → f (g b) == b
        f-g b = tpt-eqv-fst (ua b) prop-has-all-paths-↓ ∙ coe-equiv-β b
        g-f : (a : X , φ₁ == Y , φ₂) → g (f a) == a
        g-f idp = pair== (ua-η idp) prop-has-all-paths-↓ ∙ ! (pair=-η idp)
          where instance _ = snd P X

finite-SubtypeProp : SubtypeProp Type₀ (lsucc lzero)
finite-SubtypeProp = is-finite , ⟨⟩

finite-types-is-univ : is-univ-fib (fst {A = Type₀} {is-finite})
finite-types-is-univ = Subtype-is-univ finite-SubtypeProp

-----------------------------------------------------------------------------
