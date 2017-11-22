{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module PiFin+.Semantics where

open import HoTT
  -- this is tedious to maintain
  -- using (Type; Type₀; Type₁; lsucc; lmax; lzero;
  --        of-type; -- syntax u :> A
  --        _∘_; is-inj;
  --        ⊥; ⊥-elim;
  --        ⊤; unit;
  --        ℕ; O; S;
  --        _⊔_; inl; inr;
  --        Σ; _,_ ; fst; snd; pair=; fst=; ↓-Σ-in;
  --        Ptd; ⊙[_,_]; pt;
  --        Trunc; [_]; Trunc-elim; Trunc=-equiv;
  --        _==_; idp; !; _∙_; ap; ua; coe; coe-equiv;
  --        PathOver; -- syntax u == v [ B ↓ p ]
  --        _≃_; is-equiv; is-eq; equiv; transport-equiv; –>; <–;
  --        has-level-in; is-contr; is-prop; is-connected;
  --        inhab-prop-is-contr; prop-has-all-paths; prop-has-all-paths-↓;
  --        SubtypeProp; Trunc-level; ℕ₋₂; has-level; transport; Subtype=;
  --        Subtype=-econv; equiv-preserves-level; universe-=-level;
  --        is-set; ⟨-2⟩; is-gpd; ⊔-level; ⟨⟩; _⁻¹;
  --        has-dec-eq; Dec; inr=inr-equiv; dec-eq-is-set;
  --        Subtype=-out; coe-equiv-β; pair==; ua-η; pair=-η;
  --        )

-----------------------------------------------------------------------------
-- A path between ⊤ ⊔ X and ⊤ ⊔ Y induces a path between X and Y
-- Proof is tedious combinatorics

inl!=inr : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
          {a : A} {b : B} → (inl a == inr b) → C
inl!=inr ()

module _ {ℓ} {X Y : Type ℓ}
         (f : ⊤ ⊔ X → ⊤ ⊔ Y) (g : ⊤ ⊔ Y → ⊤ ⊔ X)
         (g-f : (x : ⊤ ⊔ X) → g (f x) == x) where

  finj : {x : X} → (p : f (inl unit) == f (inr x)) → inl unit == inr x
  finj p = ! (g-f (inl unit)) ∙ -- inl unit = g (f (inl unit))
           ap g p ∙             -- g (f (inl unit)) == g (f (inr x))
           (g-f (inr _))        -- g (f (inr x)) = inr x

module _ {ℓ} {X Y : Type ℓ}
         (f : ⊤ ⊔ X → ⊤ ⊔ Y) (g : ⊤ ⊔ Y → ⊤ ⊔ X)
         (f-g : (y : ⊤ ⊔ Y) → f (g y) == y)
         (g-f : (x : ⊤ ⊔ X) → g (f x) == x) where

  reduce-aux : (x : X) →
               Σ (⊤ ⊔ Y) (λ y → f (inl unit) == y) →
               Σ (⊤ ⊔ Y) (λ y → f (inr x) == y) →
               Y
  reduce-aux x (inl unit , p) (inl unit , q) =
    inl!=inr (finj f g g-f (p ∙ ! q))
  reduce-aux x (inl unit , p) (inr y , q)    = y
  reduce-aux x (inr y , p)    (inl unit , q) = y
  reduce-aux x (inr y , p)    (inr y' , q)   = y'

  reduce : X → Y
  reduce x = reduce-aux x (f (inl unit) , idp) (f (inr x) , idp)

  reduce-aux-β : (x : X) →
                 (w : ⊤ ⊔ Y) → (p : f (inl unit) == w) →
                 (v : ⊤ ⊔ Y) → (q : f (inr x) == v) →
                 reduce x == reduce-aux x (w , p) (v , q)
  reduce-aux-β x w p v q =
    ap (λ γ → reduce-aux x γ (f (inr x) , idp)) {!!} ∙
    ap (λ γ → reduce-aux x (w , γ) (f (inr x) , idp)) {!!} ∙
    ap (λ γ → reduce-aux x (w , p) γ) {!!} ∙
    ap (λ γ → reduce-aux x (w , p) (v , γ)) {!!}

{--
   ap (λ γ → rest-aux f g η x γ (f (i₂ x) , refl _))
      (dpair= (p , refl _))
◾ ap (λ γ → rest-aux f g η x (w , γ) (f (i₂ x) , refl _))
      (tpt=l _ p (refl _) ◾ ◾unitl _)
◾ ap (λ γ → rest-aux f g η x (w , p) γ)
      (dpair= (q , (refl _)))
◾ ap (λ γ → rest-aux f g η x (w , p) (v , γ))
      (tpt=l _ q (refl _) ◾ ◾unitl _)
--}



module _ {ℓ} {X Y : Type ℓ}
         (f : ⊤ ⊔ X → ⊤ ⊔ Y) (g : ⊤ ⊔ Y → ⊤ ⊔ X)
         (f-g : (y : ⊤ ⊔ Y) → f (g y) == y)
         (g-f : (x : ⊤ ⊔ X) → g (f x) == x) where

  reduce-η-aux : (x : X) →
                 (u : Σ (⊤ ⊔ Y) (λ y → (f (inl unit)) == y)) →
                 (v : Σ (⊤ ⊔ Y) (λ y → (f (inr x)) == y)) →
                 (Σ (⊤ ⊔ X) (λ y → g (inl unit) == y)) →
                 (Σ (⊤ ⊔ X) (λ y → g (fst u) == y)) →
                 (Σ (⊤ ⊔ X) (λ y → g (fst v) == y)) →
                 reduce g f g-f f-g (reduce f g f-g g-f x) == x
  reduce-η-aux x (inl unit , p) (inl unit , q) _ _ _ =
    inl!=inr (finj f g g-f (p ∙ (! q) ))
  reduce-η-aux x (u , p) (v , q) _ (inl unit , r) (inl unit , s) =
    inl!=inr
      (finj f g g-f
        (p ∙ (! (f-g u) ∙ ap f r ∙ ! (ap f s) ∙ f-g v) ∙ ! q))
  reduce-η-aux x (inr y , p) (inr y' , q) (inl unit , t)
    (inl unit , r) (inr x'' , s) =
    inl!=inr (! (! (f-g _) ∙ ap f (r ∙ ! t) ∙ (f-g _)))
  reduce-η-aux x (_ , p) _ _ (inr _ , r) _ =
    inl!=inr (finj f g g-f (p ∙ ! (f-g _) ∙ ap f r))
  reduce-η-aux x (inr y , p) (inr y' , q) (inr x' , t)
    (inl unit , r) (inr x'' , s) =
    {!!}
  reduce-η-aux x (inl unit , p) (inr y' , q) _
    (inl unit , r) (inr x'' , s) =
    {!!}
  reduce-η-aux x (inr y , p) (inl unit , q) _
    (inl unit , r) (inr x'' , s) =
    {!!}

  reduce-η : (x : X) → reduce g f g-f f-g (reduce f g f-g g-f x) == x
  reduce-η x = reduce-η-aux x
                 (f (inl unit) , idp)
                 (f (inr x) , idp)
                 (g (inl unit) , idp)
                 (g (f (inl unit)) , idp)
                 (g (f (inr x)) , idp)

⊤-cncl : ∀ {ℓ} {X Y : Type ℓ} → ⊤ ⊔ X == ⊤ ⊔ Y → X == Y
⊤-cncl = ua ∘ ⊤-cncl≃ ∘ coe-equiv
  where
    ⊤-cncl≃ : ∀ {ℓ} {X Y : Type ℓ} → (⊤ ⊔ X ≃ ⊤ ⊔ Y) → (X ≃ Y)
    ⊤-cncl≃ (f , record { g = g ; f-g = f-g ; g-f = g-f ; adj = adj }) =
      reduce f g f-g g-f ,
      is-eq
        _
        (reduce g f g-f f-g)
        (reduce-η g f g-f f-g)
        (reduce-η f g f-g g-f)

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

-- port over from EmbeddingsInUniverse
is-finite-path : (X : Type₀) → (φ₁ φ₂ : is-finite X) → φ₁ == φ₂
is-finite-path X (O , ψ₁) (O , ψ₂) = pair= idp (prop-has-all-paths ψ₁ ψ₂)
is-finite-path X (O , ψ₁) (S m , ψ₂) = ⊥-elim (Trunc-elim (λ p → coe p (inl unit)) (Trunc-fmap2 _∙_ ψ₂ (Trunc-fmap ! ψ₁)))
is-finite-path X (S n , ψ₁) (O , ψ₂) = ⊥-elim (Trunc-elim (λ p → coe p (inl unit)) (Trunc-fmap2 _∙_ ψ₁ (Trunc-fmap ! ψ₂)))
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
finite-SubtypeProp = is-finite , is-finite-is-prop

finite-types-is-univ : is-univ-fib (fst {A = Type₀} {is-finite})
finite-types-is-univ = Subtype-is-univ finite-SubtypeProp

-----------------------------------------------------------------------------

2-paths-in-ℕ : (m n : ℕ) (p : m == n) → p == idp [ (λ x → x == n) ↓ p ]
2-paths-in-ℕ m .m idp = idp

2-paths-in-El : {n : ℕ} (x y : El n) (p : x == y) → p == idp [ (λ z → z == y) ↓ p ]
2-paths-in-El x .x idp = idp

⊔-unit-l-eqv : ∀ {ℓ} (X : Type ℓ) → ⊥ ⊔ X ≃ X
⊔-unit-l-eqv X = equiv f g f-g g-f
  where f : ⊥ ⊔ X → X
        f (inl ())
        f (inr x) = x
        g : X → ⊥ ⊔ X
        g = inr
        f-g : (b : X) → b == b
        f-g b = idp
        g-f : (a : ⊥ ⊔ X) → g (f a) == a
        g-f (inl ())
        g-f (inr x) = idp

⊔-unit-l : ∀ {ℓ} (X : Type ℓ) → ⊥ ⊔ X == X
⊔-unit-l = ua ∘ ⊔-unit-l-eqv

⊔-unit-r-eqv : ∀ {ℓ} (X : Type ℓ) → X ⊔ ⊥ ≃ X
⊔-unit-r-eqv X = equiv f g f-g g-f
  where f : X ⊔ ⊥ → X
        f (inl x) = x
        f (inr ())
        g : X → X ⊔ ⊥
        g = inl
        f-g : (b : X) → b == b
        f-g b = idp
        g-f : (a : X ⊔ ⊥) → g (f a) == a
        g-f (inl x) = idp
        g-f (inr ())

⊔-unit-r : ∀ {ℓ} (X : Type ℓ) → X ⊔ ⊥ == X
⊔-unit-r = ua ∘ ⊔-unit-r-eqv

⊔-assoc-eqv : ∀ {ℓ} (X Y Z : Type ℓ) → X ⊔ (Y ⊔ Z) ≃ (X ⊔ Y) ⊔ Z
⊔-assoc-eqv X Y Z = equiv f g f-g g-f
  where f : X ⊔ (Y ⊔ Z) → (X ⊔ Y) ⊔ Z
        f (inl x) = inl (inl x)
        f (inr (inl y)) = inl (inr y)
        f (inr (inr z)) = inr z
        g : (X ⊔ Y) ⊔ Z → X ⊔ (Y ⊔ Z)
        g (inl (inl x)) = inl x
        g (inl (inr y)) = inr (inl y)
        g (inr z) = inr (inr z)
        f-g : (b : (X ⊔ Y) ⊔ Z) → f (g b) == b
        f-g (inl (inl x)) = idp
        f-g (inl (inr y)) = idp
        f-g (inr z) = idp
        g-f : (a : X ⊔ (Y ⊔ Z)) → g (f a) == a
        g-f (inl x) = idp
        g-f (inr (inl y)) = idp
        g-f (inr (inr z)) = idp

⊔-assoc : ∀ {ℓ} (X Y Z : Type ℓ) → X ⊔ (Y ⊔ Z) == (X ⊔ Y) ⊔ Z
⊔-assoc X Y Z = ua (⊔-assoc-eqv X Y Z)

⊔-comm-eqv : ∀ {ℓ} (X Y : Type ℓ) → X ⊔ Y ≃ Y ⊔ X
⊔-comm-eqv X Y = equiv f g f-g g-f
  where f : X ⊔ Y → Y ⊔ X
        f (inl x) = inr x
        f (inr y) = inl y
        g : Y ⊔ X → X ⊔ Y
        g (inl y) = inr y
        g (inr x) = inl x
        f-g : (b : Y ⊔ X) → f (g b) == b
        f-g (inl y) = idp
        f-g (inr x) = idp
        g-f : (a : X ⊔ Y) → g (f a) == a
        g-f (inl x) = idp
        g-f (inr y) = idp

⊔-comm : ∀ {ℓ} (X Y : Type ℓ) → X ⊔ Y == Y ⊔ X
⊔-comm X Y = ua (⊔-comm-eqv X Y)

⊔-comm-eqv-inv : ∀ {ℓ} (X Y : Type ℓ) → ⊔-comm-eqv X Y == ⊔-comm-eqv Y X ⁻¹
⊔-comm-eqv-inv X Y = pair= p prop-has-all-paths-↓
  where p : –> (⊔-comm-eqv X Y) == <– (⊔-comm-eqv Y X)
        p = λ= λ { (inl x) → idp ; (inr x) → idp }

ide⁻¹ : ∀ {ℓ} {X : Type ℓ} → (ide X) ⁻¹ == ide X
ide⁻¹ {X = X} = pair= idp (prop-has-all-paths (is-equiv-inverse (idf-is-equiv X)) (idf-is-equiv X))

ua⁻¹ : ∀ {ℓ} {X Y : Type ℓ} (e : X ≃ Y) → ua (e ⁻¹) == ! (ua e)
ua⁻¹ e = equiv-induction (λ eq → ua (eq ⁻¹) == ! (ua eq))
                         (λ A → ((ap ua ide⁻¹) ∙ (ua-η idp)) ∙ (ap ! (! (ua-η idp)))) e

⊔-comm-inv : ∀ {ℓ} (X Y : Type ℓ) → ⊔-comm X Y == ! (⊔-comm Y X)
⊔-comm-inv X Y = (ap ua (⊔-comm-eqv-inv X Y)) ∙ ua⁻¹ (⊔-comm-eqv Y X)

El-+ : (m n : ℕ) → El (m + n) == (El m ⊔ El n)
El-+ O n = ! (⊔-unit-l (El n))
El-+ (S m) n = ap (λ X → ⊤ ⊔ X) (El-+ m n) ∙ ⊔-assoc ⊤ (El m) (El n)

inl-El : {n : ℕ} → El (S n)
inl-El = inl tt

inr-El : (m : ℕ) → {n : ℕ} → El (S n)
inr-El O {n} = inl tt
inr-El (S m) {O} = inl tt
inr-El (S m) {S n} = inr (inr-El m {n})

`id : {m n : ℕ} (p : m == n) → El m == El n
`id = ap El

`id-coe-β : {n : ℕ} (p : n == n) (x : El n) → coe (`id p) x == x
`id-coe-β {n} p x = (ap (λ p → coe (ap El p) x) (prop-has-all-paths p idp))

`unite₊l : (n : ℕ) → El (0 + n) == El n
`unite₊l n = El-+ O n
           ∙ ⊔-unit-l (El n)

`unite₊l-coe-β : {n : ℕ} → (x : El n) → coe (`unite₊l n) x == x
`unite₊l-coe-β {O} ()
`unite₊l-coe-β {S n} x = ap (λ p → coe p x) (!-inv-l (⊔-unit-l (El (S n))))

`unite₊r : (n : ℕ) → El (n + 0) == El n
`unite₊r n = El-+ n 0
           ∙ ⊔-unit-r (El n)

`unite₊r-El : {n : ℕ} → El (n + 0) → El n
`unite₊r-El {n} x = –> (⊔-unit-r-eqv (El n)) (coe (El-+ n O) x)

`unite₊r-coe-β : {n : ℕ} → (x : El (n + 0)) → coe (`unite₊r n) x == `unite₊r-El x
`unite₊r-coe-β {n} x = coe-∙ (El-+ n O) (⊔-unit-r (El n)) x
                     ∙ coe-β (⊔-unit-r-eqv (El n)) (coe (El-+ n O) x)

`swap₊ : (m n : ℕ) → El (m + n) == El (n + m)
`swap₊ m n = El-+ m n
           ∙ ⊔-comm (El m) (El n)
           ∙ ! (El-+ n m)

`swap₊-El : {m n : ℕ} → El (m + n) → El (n + m)
`swap₊-El {m} {n} x = coe (! (El-+ n m)) (–> (⊔-comm-eqv (El m) (El n)) (coe (El-+ m n) x))

coe-∙∙ : ∀ {i} {A B C D : Type i} (p : A == B) (q : B == C) (r : C == D) (a : A)
       → coe (p ∙ q ∙ r) a == coe r (coe q (coe p a))
coe-∙∙ p q r a = (coe-∙ p (q ∙ r) a) ∙ (coe-∙ q r (coe p a))

`swap₊-coe-β : {m n : ℕ} → (x : El (m + n)) → coe (`swap₊ m n) x == `swap₊-El {m} {n} x
`swap₊-coe-β {m} {n} x = coe-∙∙ (El-+ m n) (⊔-comm (El m) (El n)) (! (El-+ n m)) x
                       ∙ ap (coe (! (El-+ n m)))
                            (coe-β (⊔-comm-eqv (El m) (El n))
                                   (coe (El-+ m n) x))

`assocl₊ : (m n o : ℕ) → El (m + (n + o)) == El ((m + n) + o)
`assocl₊ m n o = El-+ m (n + o)
               ∙ ap (λ X → El m ⊔ X) (El-+ n o)
               ∙ ⊔-assoc (El m) (El n) (El o)
               ∙ ! (ap (λ X → X ⊔ El o) (El-+ m n))
               ∙ ! (El-+ (m + n) o)

`assocl₊-El : {m n o : ℕ} → El (m + (n + o)) → El ((m + n) + o)
`assocl₊-El {m} {n} {o} x = coe (! (El-+ (m + n) o))
                              (coe (! (ap (λ X → X ⊔ El o) (El-+ m n)))
                                (–> (⊔-assoc-eqv (El m) (El n) (El o))
                                  (coe (ap (λ X → El m ⊔ X) (El-+ n o))
                                    (coe (El-+ m (n + o)) x))))

coe-∙∙∙∙ : ∀ {i} {A B C D E F : Type i} (p : A == B) (q : B == C) (r : C == D) (s : D == E) (t : E == F) (a : A)
         → coe (p ∙ q ∙ r ∙ s ∙ t) a == coe t (coe s (coe r (coe q (coe p a))))
coe-∙∙∙∙ p q r s t a = coe-∙∙ p q (r ∙ s ∙ t) a ∙ coe-∙∙ r s t (coe q (coe p a))

`assocl₊-El-β : {m n o : ℕ} → (x : El (m + (n + o))) → coe (`assocl₊ m n o) x == `assocl₊-El {m} {n} {o} x
`assocl₊-El-β {m} {n} {o} x = coe-∙∙∙∙ (El-+ m (n + o)) (ap (λ X → El m ⊔ X) (El-+ n o))
                                       (⊔-assoc (El m) (El n) (El o))
                                       (! (ap (λ X → X ⊔ El o) (El-+ m n))) (! (El-+ (m + n) o)) x
                            ∙ ap (coe ((! (El-+ (m + n) o))))
                                 (ap (coe ((! (ap (λ X → Coprod X (El o)) (El-+ m n)))))
                                     (coe-β (⊔-assoc-eqv (El m) (El n) (El o))
                                            (coe (ap (λ X → Coprod (El m) X) (El-+ n o))
                                                 (coe (El-+ m (n + o)) x))))

`swap₊² : (m n : ℕ) → El (m + n) == El (m + n)
`swap₊² m n = `swap₊ m n ∙ `swap₊ n m

`swap₊²=idp : (m n : ℕ) → `swap₊² m n == idp
`swap₊²=idp m n = path (El-+ m n) (⊔-comm (El m) (El n)) (⊔-comm (El n) (El m))
                       (El-+ n m) (⊔-comm-inv (El m) (El n))
  -- could be done with assoc but tedious
  where path : ∀ {ℓ} {X : Type ℓ} {a b c d : X}
             → (p : a == b) (q : b == c) (q' : c == b) (r : d == c)
             → (α : q == ! q')
             → (p ∙ q ∙ ! r) ∙ (r ∙ q' ∙ ! p) == idp
        path idp q q' idp α = ap (λ z → (q ∙ idp) ∙ z) (∙-unit-r q')
                            ∙ (ap (λ z → z ∙ q') (∙-unit-r q))
                            ∙ ((ap (λ z → z ∙ q') α) ∙ (!-inv-l q'))
