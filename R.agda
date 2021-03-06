{-# OPTIONS --without-K #-}

module R where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function renaming (_∘_ to _○_)
open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Product as C
open import Categories.Groupoid.Product as G
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Nat hiding (_⊔_)
open import Data.Integer as ℤ hiding (_⊔_)

------------------------------------------------------------------------------
-- Featherweight HoTT !

-- Each universe has:
--   * code U for types
--   * an interpretation El of these codes as spaces
--   * a semantic notion of equivalence on the interpretations
-- [Really we want codes for a category and an actual category.]

-- The first universe (level 0) consists of just the finite types and
-- isomorphisms between them.

-- Once we have that level 0 universe, we can define a new universe (level 1)
-- whose codes are the equivalences at level 0. We then define a notion of
-- equivalence at level 1 that identifies some level 0 equivalences.

-- We can now define a level 2 universe whose codes are the level 1
-- equivalences. We then repeat and define a notion of equivalence at level 2
-- that identifies some level 1 equivalences.

-- Then we have some additional interesting things:

--   * Univalence at the lowest levels identifies level 0 equivalences and level
--     1 codes. The interesting direction verifies that the level 1 codes are
--     complete with respect to the level 0 equivalences

--   * Once we get to level 2, we can define additional interesting semantic
--     notions like higher inductive types by using equivalences from lower
--     levels. In particular we show at level 2 that an equivalence of order n
--     induces a groupoid of cardinality 1/n. We can then at level 3 introduce
--     codes for these fractional groupoids. Note that to define S¹ we would
--     need an equivalence of infinite order but our toy language only includes
--     finite types.

------------------------------------------------------------------------------
-- The type of universes.

record UNIVERSE : Set₁ where
  field
    -- codes
    U   : Set
    -- decoding a code to a space
    El  : U → Set
    -- the type of functions from spaces to spaces
    Fun : (A B : U) → Set
    -- identity relation on points in a space
    _≡_ : {A : U} (a b : El A) → Set
    -- homotopy of functions from spaces to spaces
    _∼_ : {A B : U} (f g : Fun A B) → Set
    -- equivalence of spaces El A and El B
    _≃_ : (A B : U) → Set

record UNIVERSE2 : Set₂ where
  field
    -- codes
    U   : Set
    -- decoding a code to a space
    El  : U → Set₁
    -- the type of functions from spaces to spaces
    Fun : (A B : U) → Set
    -- identity relation on points in a space
    _≡_ : {A : U} (a b : El A) → Set
    -- homotopy of functions from spaces to spaces
    _∼_ : {A B : U} (f g : Fun A B) → Set
    -- equivalence of spaces El A and El B
    _≃_ : (A B : U) → Set

------------------------------------------------------------------------------
-- level 0 universe

module MOD0 where

  -- Codes of finite types

  infix 50 _⊕_
  infix 60 _⊗_

  data U : Set where
    𝟘   : U
    𝟙   : U
    _⊕_ : U → U → U
    _⊗_ : U → U → U

  -- Denotations of codes

  El : U → Set
  El 𝟘       = ⊥
  El 𝟙       = ⊤
  El (A ⊕ B) = El A ⊎ El B
  El (A ⊗ B) = El A × El B

  -- The type of functions from spaces to spaces is the regular function space

  Fun : (A B : U) → Set
  Fun A B = El A → El B

  -- Identity

  data _≡_ {A : U} : (a b : El A) → Set where
    refl : (a : El A) → (a ≡ a)

  sym≡ : {A : U} {a b : El A} → a ≡ b → b ≡ a
  sym≡ (refl a) = refl a

  trans≡ : {A : U} {a b c : El A} → a ≡ b → b ≡ c → a ≡ c
  trans≡ (refl a) (refl .a) = refl a

  cong≡ : {A B : U} {a b : El A} → (f : Fun A B) (p : a ≡ b) →
          f a ≡ f b
  cong≡ f (refl a) = refl (f a)

  -- Homotopy

  _∼_ : {A B : U} → (f g : Fun A B) → Set
  _∼_ {A} {B} f g = (a : El A) → f a ≡ g a

  refl∼ : {A B : U} → (f : Fun A B) → (f ∼ f)
  refl∼ f a = refl (f a)

  sym∼ : {A B : U} {f g : Fun A B} → (f ∼ g) → (g ∼ f)
  sym∼ H b = sym≡ (H b)

  trans∼ : {A B : U} {f g h : Fun A B} → f ∼ g → g ∼ h → f ∼ h
  trans∼ p₁ p₂ a = trans≡ (p₁ a) (p₂ a)

  ∼○ : {A B C : U} {f g : Fun A B} {h k : Fun B C} →
       (f ∼ g) → (h ∼ k) → ((h ○ f) ∼ (k ○ g))
  ∼○ {f = f} {g = g} {h = h} H₁ H₂ x = trans≡ (cong≡ h (H₁ x)) (H₂ (g x))

  -- Equivalence

  record isequiv {A B : U} (f : Fun A B) : Set where
    constructor mkisequiv
    field
      g : El B → El A
      α : (f ○ g) ∼ id
      β : (g ○ f) ∼ id

  _≃_ : (A B : U) → Set
  A ≃ B = Σ (Fun A B) isequiv

  -- Examples of equivalences

  id≃ : {A : U} → A ≃ A
  id≃ = (id , mkisequiv id refl refl)

  sym≃ : {A B : U} → A ≃ B → B ≃ A
  sym≃ (f , mkisequiv g α β) = (g , mkisequiv f β α)

  trans≃ : {A B C : U} → A ≃ B → B ≃ C → A ≃ C
  trans≃ {A} {B} {C} (f , mkisequiv f⁻ α₁ β₁) (g , mkisequiv g⁻ α₂ β₂) =
    g ○ f , mkisequiv (f⁻ ○ g⁻) α β
      where α : (x : El C) → (g (f (f⁻ (g⁻ x)))) ≡ x
            α x = trans≡ (cong≡ g (α₁ (g⁻ x))) (α₂ x)
            β : (x : El A) → (f⁻ (g⁻ (g (f x)))) ≡ x
            β x = trans≡ (cong≡ f⁻ (β₂ (f x))) (β₁ x)

  A⊎⊥≃A : {A : U} → A ⊕ 𝟘 ≃ A
  A⊎⊥≃A {A} = f , mkisequiv g refl β
    where
      f : (El A ⊎ ⊥) → El A
      f (inj₁ a) = a
      f (inj₂ ())

      g : El A → (El A ⊎ ⊥)
      g a = inj₁ a

      β : (g ○ f) ∼ id
      β (inj₁ a) = refl (inj₁ a)
      β (inj₂ ())

  -- Universe 0

  Univ : UNIVERSE
  Univ = record {
           U = U
         ; El = El
         ; Fun = Fun
         ; _≡_ = _≡_
         ; _∼_ = _∼_
         ; _≃_ = _≃_
         }

------------------------------------------------------------------------------
-- level 1 universe: codes correspond to level 0 equivalences

module MOD1 where

  open MOD0
    using    (𝟘; 𝟙; _⊕_; _⊗_)
    renaming (U to U₀; Fun to Fun₀;
              _∼_ to _∼₀_; refl∼ to refl∼₀; sym∼ to sym∼₀; trans∼ to trans∼₀;
              _≃_ to _≃₀_)

  -- Codes in level 1 for level 0 equivalences

  data _⟷_ : U₀ → U₀ → Set where
    id⟷ :    {A : U₀} → A ⟷ A
    uniti₊r : {A : U₀} → A ⟷ (A ⊕ 𝟘)
    unite₊r : {A : U₀} → A ⊕ 𝟘 ⟷ A
    _◎_ :     {A B C : U₀} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)
    -- elided

  ! : {A B : U₀} → (A ⟷ B) → (B ⟷ A)
  ! unite₊r = uniti₊r
  ! uniti₊r = unite₊r
  ! id⟷ = id⟷
  ! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁

  -- Decoding a code to a space

  El : {A B : U₀} → (A ⟷ B) → Set
  El {A} {B} _ = A ≃₀ B

  -- Every code at level 1 does correspond to a level 0 equivalence
  -- Reverse direction is univalence; addressed below

  sound : {A B : U₀} → (c : A ⟷ B) → El c
  sound id⟷ = MOD0.id≃
  sound uniti₊r = MOD0.sym≃ MOD0.A⊎⊥≃A
  sound unite₊r = MOD0.A⊎⊥≃A
  sound (c₁ ◎ c₂) = MOD0.trans≃ (sound c₁) (sound c₂)

  -- Functions between spaces (A ≃₀ B) and (A ≃₀ B). The elements of (A ≃₀ B)
  -- are functions back and forth and proofs. A function between the spaces will
  -- map each pair of functions to another pair of functions while preserving
  -- the proofs.

  Fun : {A B : U₀} → (c₁ c₂ : A ⟷ B) → Set
  Fun {A} {B} _ _ =
    Σ[ F ∈ (Fun₀ A B → Fun₀ A B) ]
    Σ[ G ∈ (Fun₀ B A → Fun₀ B A) ]
    ((f : Fun₀ A B) → (F f ∼₀ f)) ×
    ((g : Fun₀ B A) → (G g ∼₀ g))


  app : {A B : U₀} {c₁ c₂ : A ⟷ B} → Fun c₁ c₂ → El c₁ → El c₂
  app (F , G , γ , δ) (f , MOD0.mkisequiv g α β) =
    F f ,
    MOD0.mkisequiv
      (G g)
      (trans∼₀ (MOD0.∼○ (δ g) (γ f)) α)
      (trans∼₀ (MOD0.∼○ (γ f) (δ g)) β)

  idF : {A B : U₀} {c : A ⟷ B} → Fun c c
  idF = (id , id , refl∼₀ , refl∼₀)

  compose : {A B : U₀} {c₁ c₂ c₃ : A ⟷ B} → Fun c₁ c₂ → Fun c₂ c₃ → Fun c₁ c₃
  compose (F₁ , G₁ , γ₁ , δ₁) (F₂ , G₂ , γ₂ , δ₂) =
    F₂ ○ F₁ ,
    G₂ ○ G₁ ,
    (λ f → trans∼₀ (γ₂ (F₁ f)) (γ₁ f)) ,
    (λ g → trans∼₀ (δ₂ (G₁ g)) (δ₁ g))

  -- Need associativity of compose: see below where homotopy is
  -- defined, as we need a notion of 'sameness' of Fun to express it.

  -- Identity

  record _≡_ {A B : U₀} {c : A ⟷ B} (eq₁ eq₂ : El c) : Set where
    open MOD0.isequiv (proj₂ eq₁) renaming (g to g₁)
    open MOD0.isequiv (proj₂ eq₂) renaming (g to g₂)
    field
      f≡ : proj₁ eq₁ ∼₀ proj₁ eq₂
      g≡ : g₁ ∼₀ g₂

  refl≡ : {A B : U₀} {c : A ⟷ B} (eq : El c) → _≡_ {c = c} eq eq
  refl≡ (f , MOD0.mkisequiv g α β) =
    record {
      f≡ = MOD0.refl∼ f
    ; g≡ = MOD0.refl∼ g
    }

  trans≡ : {A B : U₀} {c : A ⟷ B} {eq₁ eq₂ eq₃ : El c} →
           (_≡_ {c = c} eq₁ eq₂) → (_≡_ {c = c} eq₂ eq₃) →
           (_≡_ {c = c} eq₁ eq₃)
  trans≡ (record { f≡ = f≡₁ ; g≡ = g≡₁ }) (record { f≡ = f≡₂ ; g≡ = g≡₂ }) =
    record {
      f≡ = MOD0.trans∼ f≡₁ f≡₂
    ; g≡ = MOD0.trans∼ g≡₁ g≡₂
    }

  cong≡ : {A B : U₀} {c₁ c₂ : A ⟷ B} {eq₁ eq₂ : El c₁} →
   (f : Fun c₁ c₂) → _≡_ {c = c₁} eq₁ eq₂ →
   _≡_ {c = c₂} (app {c₁ = c₁} {c₂ = c₂} f eq₁) (app {c₁ = c₁} {c₂ = c₂} f eq₂)
  cong≡ {eq₁ = f₁ , MOD0.mkisequiv g₁ α₁ β₁}
        {eq₂ = f₂ , MOD0.mkisequiv g₂ α₂ β₂}
        (F , G , γ , δ)
        (record { f≡ = f≡ ; g≡ = g≡ }) =
    record {
       f≡ = trans∼₀ (γ f₁) (trans∼₀ f≡ (sym∼₀ (γ f₂)))
     ; g≡ = trans∼₀ (δ g₁) (trans∼₀ g≡ (sym∼₀ (δ g₂)))
     }

  -- Homotopy

  _∼_ : {A B : U₀} {c₁ c₂ : A ⟷ B} → (f g : Fun c₁ c₂) → Set
  _∼_ {c₁ = c₁} {c₂ = c₂} f g =
    (eq : El c₁) →
    _≡_ {c = c₂} (app {c₁ = c₁} {c₂ = c₂} f eq) (app {c₁ = c₁} {c₂ = c₂} g eq)

  refl∼ : {A B : U₀} {c : A ⟷ B} → (f : Fun c c) →
          _∼_ {c₁ = c} {c₂ = c} f f
  refl∼ {c = c} f eq = refl≡ (app {c₁ = c} {c₂ = c} f eq)

  -- also need sym∼ and cong∼ and trans∼

  -- now we can prove that compose is associative:
  assoc-∘ : {A B : U₀} {c₁ c₂ c₃ c₄ : A ⟷ B} {f : Fun c₁ c₂} {g : Fun c₂ c₃} {h : Fun c₃ c₄} →
    _∼_ {c₁ = c₁} {c₄} (compose {c₁ = c₁} {c₂} {c₄} f (compose {c₁ = c₂} {c₃} {c₄} g h))
                       (compose {c₁ = c₁} {c₃} {c₄} (compose {c₁ = c₁} {c₂} {c₃} f g) h)
  assoc-∘ = {!!}

  -- Equivalence

  record isequiv {A B : U₀} {c₁ c₂ : A ⟷ B}
         (f : Fun c₁ c₂) : Set where
    constructor mkisequiv
    field
      g : Fun c₂ c₁
      α : _∼_ {c₁ = c₂} {c₂ = c₂}
          (compose {c₁ = c₂} {c₂ = c₁} {c₃ = c₂} g f)
          (idF {c = c₂})
      β : _∼_ {c₁ = c₁} {c₂ = c₁}
          (compose {c₁ = c₁} {c₂ = c₂} {c₃ = c₁} f g)
          (idF {c = c₁})

  _≃_ : {A B : U₀} → (c₁ c₂ : A ⟷ B) → Set
  _≃_ {A} {B} c₁ c₂ = Σ (Fun c₁ c₂) (isequiv {c₁ = c₁} {c₂ = c₂})

  -- Example level 1 equivalences

  id≃ : {A B : U₀} → (c : A ⟷ B) → c ≃ c
  id≃ c = idF {c = c},
          mkisequiv
            (idF {c = c})
            (refl∼ {c = c} (idF {c = c}))
            (refl∼ {c = c} (idF {c = c}))

  -- the proofs below need trans∼ and inv∼, but then are straightforward.
  trans≃ : {A B : U₀} {c₁ c₂ c₃ : A ⟷ B} → (c₁ ≃ c₂) → (c₂ ≃ c₃) → (c₁ ≃ c₃)
  trans≃ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}
    (f , mkisequiv f⁻ α₁ β₁) (g , mkisequiv g⁻ α₂ β₂) =
    compose {c₁ = c₁} {c₂ = c₂} {c₃ = c₃} f g ,
    mkisequiv (compose {c₁ = c₃} {c₂ = c₂} {c₃ = c₁} g⁻ f⁻)
    (λ eq₁ → {!!})
    (λ eq₂ → {!!})

  -- Universe 1

  Univ : (A B : U₀) → UNIVERSE
  Univ A B = record {
               U = A ⟷ B
             ; El = λ _ → A ≃₀ B
             ; Fun = Fun
             ; _≡_ = λ { {c} → _≡_ {c = c}}
             ; _∼_ = λ { {c₁} {c₂} → _∼_ {c₁ = c₁} {c₂ = c₂}}
             ; _≃_ = _≃_
             }

------------------------------------------------------------------------------
-- level 0-1 cross equivalences

module MOD0x1 where

  open MOD0
    using    ()
    renaming (U to U₀; _∼_ to _∼₀_; _≃_ to _≃₀_)

  open MOD1
    using    (_⟷_; id⟷; uniti₊r; unite₊r; _◎_; sound)
    renaming (_≡_ to _≡₁_; _≃_ to _≃₁_)

  -- We want to make sure that the level 1 codes are exactly the level 0
  -- equivalences. We will define a cross-level equivalence between them: that
  -- is univalence!

  -- The two spaces in question are:
  -- A ≃₀ B in level 0 universe, and
  -- A ⟷ B in level 1 universe
  -- We need functions going in both directions that are inverses
  -- from A ⟷ B to A ≃₀ B we have the function sound in MOD1
  -- from A ≃₀ B to A ⟷ B we have the function complete below

  complete : {A B : U₀} → (A ≃₀ B) → (A ⟷ B)
  complete {A} {B} (f , MOD0.mkisequiv g α β) = {!!}

  -- Now we need to require inverses

  record univalence {A B : U₀} : Set where
    field
      α : (c : A ⟷ B) → complete (sound c) ≃₁ c
      β : (eq : A ≃₀ B) → Σ[ c ∈ A ⟷ B ] _≡₁_ {c = c} (sound (complete eq)) eq

------------------------------------------------------------------------------
-- level 2 universe: codes for level 1 equivalences

module MOD2 where

  open MOD0
    using ()
    renaming (U to U₀)

  open MOD1
    using (_⟷_; id⟷; _◎_; !)
    renaming (_≃_ to _≃₁_; id≃ to id≃₁; trans≃ to trans≃₁)

  -- Codes in level 2 for level 1 equivalences

  data _⇔_ : {A B : U₀} → (A ⟷ B) → (A ⟷ B) → Set where
    id⇔ : ∀ {A B} {c : A ⟷ B} → c ⇔ c
    _●_  : ∀ {A B} {c₁ c₂ c₃ : A ⟷ B} → (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)

  2! : {A B : U₀} {c₁ c₂ : A ⟷ B} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
  2! id⇔ = id⇔
  2! (α ● β) = (2! β) ● (2! α)

  -- Decoding a code to a space

  El : {A B : U₀} {c₁ c₂ : A ⟷ B} → (α : c₁ ⇔ c₂) → Set
  El {c₁ = c₁} {c₂ = c₂} _ = c₁ ≃₁ c₂

  -- Every code at level 2 does correspond to a level 1 equivalence
  -- Reverse direction is univalence; addressed below

  sound : {A B : U₀} {c₁ c₂ : A ⟷ B} → (α : c₁ ⇔ c₂) → El α
  sound {c₁ = c} {c₂ = .c} id⇔ = id≃₁ c
  sound (α₁ ● α₂) = trans≃₁ (sound α₁) (sound α₂)

  -- Type of functions

  Fun : {A B : U₀} {c₁ c₂ : A ⟷ B} → (α β : c₁ ⇔ c₂) → Set
  Fun {A} {B} {c₁} {c₂} α β = {!!}

{--
  -- semantic notions on Univ₂:
  -- (1) when are two interpretations equivalent

  record _≡₂_ {A B : U₀} {c₁ c₂ : A ⟷ B} {α β : c₁ ⇔ c₂}
              (eq₁ : El α) (eq₂ : El β) : Set where
    open MOD1.isequiv (proj₂ eq₁) renaming (g to g₁)
    open MOD1.isequiv (proj₂ eq₂) renaming (g to g₂)
    field
      f≡ : _∼₁_ {c₁ = c₁} {c₂ = c₂} (proj₁ eq₁) (proj₁ eq₂)
      g≡ : _∼₁_ {c₁ = c₂} {c₂ = c₁} g₁ g₂

  _∼₂_ : {A B C D : U₀} {c₁ c₂ : A ⟷ B} {d₁ d₂ : C ⟷ D}
         {α : c₁ ⇔ c₂} {β : d₁ ⇔ d₂} → (f g : EL2 α → EL2 β) → Set
  _∼₂_ {α = α} {β = β} f g =
    (eq : EL2 α) → _≡₂_ {α = β} {β = β} (f eq) (g eq)

  record isequiv₂ {A B C D : U₀} {c₁ c₂ : A ⟷ B} {d₁ d₂ : C ⟷ D}
         {Α : c₁ ⇔ c₂} {Β : d₁ ⇔ d₂} (f : EL2 Α → EL2 Β) : Set where
    constructor mkisequiv₂
    field
      g : EL2 Β → EL2 Α
      α : _∼₂_ {α = Β} {β = Β} (f ○ g) id
      β : _∼₂_ {α = Α} {β = Α} (g ○ f) id

  _≃₂_ : {A B C D : U₀} {c₁ c₂ : A ⟷ B} {d₁ d₂ : C ⟷ D}
         (Α : c₁ ⇔ c₂) (Β : d₁ ⇔ d₂) → Set
  Α ≃₂ Β = Σ (EL2 Α → EL2 Β) (isequiv₂ {Α = Α} {Β = Β})
--}

  -- univalence for level 2: relates level 1 equivalences with level 2 codes for
  -- these equivalences
  -- ??

  -- (2) semantic quotients on types

  infix 40 _^_

  _^_ : {t : U₀} → (p : t ⟷ t) → (k : ℤ) → (t ⟷ t)
  p ^ (+ 0) = id⟷
  p ^ (+ (suc k)) = p ◎ (p ^ (+ k))
  p ^ -[1+ 0 ] = ! p
  p ^ (-[1+ (suc k) ]) = (! p) ◎ (p ^ -[1+ k ])

  record Iter {t : U₀} (p : t ⟷ t) : Set where
    constructor <_,_,_>
    field
      k : ℤ
      q : t ⟷ t
      α : q ⇔ p ^ k

  orderC : {t : U₀} → (t ⟷ t) → Category lzero lzero lzero
  orderC p = record {
     Obj = Iter p
   ; _⇒_ = λ p^i p^j → Iter.q p^i ⇔ Iter.q p^j
   ; _≡_ = λ _ _ → ⊤
   ; id  = id⇔
   ; _∘_ = flip _●_
   ; assoc = tt
   ; identityˡ = tt
   ; identityʳ = tt
   ; equiv = record
     { refl = tt
     ; sym = λ _ → tt
     ; trans = λ _ _ → tt
     }
   ; ∘-resp-≡ = λ _ _ → tt
   }

  orderG : {t : U₀} → (p : t ⟷ t) → Groupoid (orderC p)
  orderG {U₀} p = record {
      _⁻¹ = 2!
    ; iso = λ {a} {b} {f} → record {
          isoˡ = tt
        ; isoʳ = tt
        }
    }

  -- Universe 2

  Univ : {A B : U₀} (c₁ c₂ : A ⟷ B) → UNIVERSE
  Univ c₁ c₂ = record {
             U = c₁ ⇔ c₂
           ; El = El
           ; Fun = Fun
           ; _≡_ = {!!}
           ; _∼_ = {!!}
           ; _≃_ = {!!}
           }

------------------------------------------------------------------------------
-- fractionals
-- level 3 universe: codes for level 2 quotients

module MOD3 where

  open MOD0
    using ()
    renaming (U to U₀)

  open MOD1
    using (_⟷_)
    renaming ()

  open MOD2
    using (orderG)
    renaming ()

  -- Codes for level 3 are HIT corresponding to level 2 fractional groupoids

  data U : Set where
    # : {t : U₀} → (t ⟷ t) → U
    1/# : {t : U₀} → (c : t ⟷ t) → U
    _⊠_ : U → U → U

  -- Each code denotes a groupoid

  El : U → Set₁
  El = λ A → Σ[ C ∈ Category lzero lzero lzero ] (Groupoid C)

  sound : (A : U) → El A
  sound (# c) = _ , orderG c
  sound (1/# c) = {!!}
  sound (A ⊠ B) with sound A | sound B
  ... | (C₁ , G₁) | (C₂ , G₂) = C.Product C₁ C₂ , G.Product G₁ G₂

  -- Type of functions

  Fun : (A B : U) → Set
  Fun A B = {!!}

  -- Identity

  -- Homotopy

  -- Equivalence

  Univ₃ : UNIVERSE2
  Univ₃ = record {
            U = U
          ; El = El
          ; Fun = Fun
          ; _≡_ = {!!}
          ; _∼_ = {!!}
          ; _≃_ = {!!}
          }

------------------------------------------------------------------------------
