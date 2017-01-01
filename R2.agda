{-# OPTIONS --without-K #-}

module R2 where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function renaming (_∘′_ to _○_)
open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Product as C
open import Categories.Groupoid.Product as G
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Nat hiding (_⊔_)
open import Data.Integer as ℤ hiding (_⊔_)

------------------------------------------------------------------------------
-- Featherweight HoTT !

-- Each universe has:
--   * code U for types; morphisms between codes; etc; a category
--   * an interpretation El of these codes as spaces; a category of spaces

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

record UNIVERSE {u e : Level} : Set (lsuc (u ⊔ e)) where
  field
    -- codes; morphisms on codes; code category
    U : Set u
    _⟷_ : U → U → Set
    id⟷ : {A : U} → A ⟷ A
    _◎⟷_ : {A B C : U} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)
    -- decoding a code to a space; morphisms on spaces
    El  : U → Set e
    Fun : (A B : U) → Set u
    app : {A B : U} → Fun A B → El A → El B
    idF : {A : U} → Fun A A
    _◎_ : {A B C : U} → Fun B C → Fun A B → Fun A C
    -- identity of elements of spaces; homotopies; equivalences
    _≡_ : {A : U} (a b : El A) → Set e
    id≡ : {A : U} (a : El A) → a ≡ a
    sym≡ : {A : U} {a b : El A} → a ≡ b → b ≡ a
    trans≡ : {A : U} {a b c : El A} → a ≡ b → b ≡ c → a ≡ c
    cong≡ : {A B : U} {a b : El A} → (f : Fun A B) (p : a ≡ b) → app f a ≡ app f b
    _∼_ : {A B : U} (f g : Fun A B) → Set e
    refl∼ : {A B : U} → (f : Fun A B) → (f ∼ f)
    sym∼ : {A B : U} {f g : Fun A B} → (f ∼ g) → (g ∼ f)
    trans∼ : {A B : U} {f g h : Fun A B} → f ∼ g → g ∼ h → f ∼ h
    _≃_ : (A B : U) → Set e
    id≃ : {A : U} → A ≃ A
    sym≃ : {A B : U} → A ≃ B → B ≃ A
    trans≃ : {A B C : U} → A ≃ B → B ≃ C → A ≃ C

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

  -- Morphisms on code

  data _⟷_ : U → U → Set where
    id⟷ :    {A : U} → A ⟷ A
    uniti₊r : {A : U} → A ⟷ (A ⊕ 𝟘)
    unite₊r : {A : U} → A ⊕ 𝟘 ⟷ A
    _◎_ :     {A B C : U} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)
    -- elided

  ! : {A B : U} → (A ⟷ B) → (B ⟷ A)
  ! unite₊r = uniti₊r
  ! uniti₊r = unite₊r
  ! id⟷ = id⟷
  ! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁

  -- Denotations of codes

  El : U → Set
  El 𝟘       = ⊥
  El 𝟙       = ⊤
  El (A ⊕ B) = El A ⊎ El B
  El (A ⊗ B) = El A × El B

  -- The type of functions from spaces to spaces is the regular function space

  Fun : (A B : U) → Set
  Fun A B = El A → El B

  -- Functions can be applied

  app : {A B : U} → Fun A B → El A → El B
  app f a = f a

  -- Identity

  data _≡_ {A : U} : (a b : El A) → Set where
    refl : (a : El A) → (a ≡ a)

  id≡ : {A : U} (a : El A) → a ≡ a
  id≡ a = refl a

  sym≡ : {A : U} {a b : El A} → a ≡ b → b ≡ a
  sym≡ (refl a) = refl a

  trans≡ : {A : U} {a b c : El A} → a ≡ b → b ≡ c → a ≡ c
  trans≡ (refl a) (refl .a) = refl a

  cong≡ : {A B : U} {a b : El A} → (f : Fun A B) (p : a ≡ b) →
          app f a ≡ app f b
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

  -- Non-traditional packaging of an equivalence: rather than as a property of a
  -- function, it is directly a type

  record _≃_ (A B : U) : Set where
    constructor eq
    field
      f : Fun A B
      g : Fun B A
      α : (f ○ g) ∼ id
      β : (g ○ f) ∼ id

  -- Fundamental equivalences

  id≃ : {A : U} → A ≃ A
  id≃ = eq id id refl refl

  sym≃ : {A B : U} → A ≃ B → B ≃ A
  sym≃ (eq f g α β) = eq g f β α

  trans≃ : {A B C : U} → A ≃ B → B ≃ C → A ≃ C
  trans≃ {A} {B} {C} (eq f f⁻ α₁ β₁) (eq g g⁻ α₂ β₂) =
    eq (g ○ f) (f⁻ ○ g⁻) α β
      where α : (x : El C) → (g (f (f⁻ (g⁻ x)))) ≡ x
            α x = trans≡ (cong≡ g (α₁ (g⁻ x))) (α₂ x)
            β : (x : El A) → (f⁻ (g⁻ (g (f x)))) ≡ x
            β x = trans≡ (cong≡ f⁻ (β₂ (f x))) (β₁ x)

  -- Further examples

  A⊎⊥≃A : {A : U} → A ⊕ 𝟘 ≃ A
  A⊎⊥≃A {A} = eq f g refl β
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
         ; _⟷_ = _⟷_
         ; id⟷ = id⟷
         ; _◎⟷_ = _◎_
         ; El = El
         ; Fun = Fun
         ; idF = id
         ; app = app
         ; _◎_ = _○_
         ; _≡_ = _≡_
         ; _∼_ = _∼_
         ; _≃_ = _≃_
         ; id≡ = id≡
         ; sym≡ = sym≡
         ; trans≡ = trans≡
         ; cong≡ = cong≡
         ; refl∼ = refl∼
         ; sym∼ = sym∼
         ; trans∼ = trans∼
         ; id≃ = id≃
         ; sym≃ = sym≃
         ; trans≃ = trans≃
         }

------------------------------------------------------------------------------
-- level 1 universe for each A and B: codes correspond to level 0 equivalences

module MOD1 (A B : MOD0.U) where

  open MOD0
    using    (𝟘; 𝟙; _⊕_; _⊗_; _⟷_)
    renaming (U to U₀; Fun to Fun₀;
              _∼_ to _∼₀_; refl∼ to refl∼₀; sym∼ to sym∼₀; trans∼ to trans∼₀;
              _≃_ to _≃₀_)

  -- Codes in level 1 for level 0 equivalences

  U : Set
  U = A ⟷ B

  data _⇔_ : U → U → Set where
    id⇔ : {c : U} → c ⇔ c
    _●_  : {c₁ c₂ c₃ : U} → (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)

  2! : {c₁ c₂ : U} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
  2! id⇔ = id⇔
  2! (α ● β) = (2! β) ● (2! α)

  -- Decoding a code to a space

  El : U → Set
  El _ = A ≃₀ B

  -- Functions between spaces (A ≃₀ B) and (A ≃₀ B). The elements of (A ≃₀ B)
  -- are functions back and forth and proofs. A function between the spaces will
  -- map each pair of functions to another pair of functions while preserving
  -- the proofs.

  Fun : (c₁ c₂ : U) → Set
  Fun _ _ =
    Σ[ F ∈ (Fun₀ A B → Fun₀ A B) ]
    Σ[ G ∈ (Fun₀ B A → Fun₀ B A) ]
    ((f : Fun₀ A B) → (F f ∼₀ f)) ×
    ((g : Fun₀ B A) → (G g ∼₀ g))

  app : {c₁ c₂ : U} → Fun c₁ c₂ → El c₁ → El c₂
  app (F , G , γ , δ) (MOD0.eq f g α β) =
    MOD0.eq (F f)
            (G g)
            (trans∼₀ (MOD0.∼○ (δ g) (γ f)) α)
            (trans∼₀ (MOD0.∼○ (γ f) (δ g)) β)

  idF : {c : U} → Fun c c
  idF = (id , id , refl∼₀ , refl∼₀)

  compose : {c₁ c₂ c₃ : U} → Fun c₁ c₂ → Fun c₂ c₃ → Fun c₁ c₃
  compose (F₁ , G₁ , γ₁ , δ₁) (F₂ , G₂ , γ₂ , δ₂) =
    F₂ ○ F₁ ,
    G₂ ○ G₁ ,
    (λ f → trans∼₀ (γ₂ (F₁ f)) (γ₁ f)) ,
    (λ g → trans∼₀ (δ₂ (G₁ g)) (δ₁ g))

  -- Need associativity of compose: see below where homotopy is
  -- defined, as we need a notion of 'sameness' of Fun to express it.

  -- Identity

  record _≡_ {c : U} (eq₁ eq₂ : El c) : Set where
    open MOD0._≃_ eq₁ renaming (f to f₁; g to g₁)
    open MOD0._≃_ eq₂ renaming (f to f₂; g to g₂)
    field
      f≡ : f₁ ∼₀ f₂
      g≡ : g₁ ∼₀ g₂

  refl≡ : {c : U} (eq : El c) → _≡_ {c = c} eq eq
  refl≡ (MOD0.eq f g α β) =
    record {
      f≡ = MOD0.refl∼ f
    ; g≡ = MOD0.refl∼ g
    }

  trans≡ : {c : U} {eq₁ eq₂ eq₃ : El c} →
           (_≡_ {c = c} eq₁ eq₂) → (_≡_ {c = c} eq₂ eq₃) →
           (_≡_ {c = c} eq₁ eq₃)
  trans≡ (record { f≡ = f≡₁ ; g≡ = g≡₁ }) (record { f≡ = f≡₂ ; g≡ = g≡₂ }) =
    record {
      f≡ = MOD0.trans∼ f≡₁ f≡₂
    ; g≡ = MOD0.trans∼ g≡₁ g≡₂
    }

  cong≡ : {c₁ c₂ : U} {eq₁ eq₂ : El c₁} →
   (f : Fun c₁ c₂) → _≡_ {c = c₁} eq₁ eq₂ →
   _≡_ {c = c₂} (app {c₁ = c₁} {c₂ = c₂} f eq₁) (app {c₁ = c₁} {c₂ = c₂} f eq₂)
  cong≡ {eq₁ = (MOD0.eq f₁ g₁ α₁ β₁)}
        {eq₂ = (MOD0.eq f₂ g₂ α₂ β₂)}
        (F , G , γ , δ)
        (record { f≡ = f≡ ; g≡ = g≡ }) =
    record {
       f≡ = trans∼₀ (γ f₁) (trans∼₀ f≡ (sym∼₀ (γ f₂)))
     ; g≡ = trans∼₀ (δ g₁) (trans∼₀ g≡ (sym∼₀ (δ g₂)))
     }

  -- Homotopy

  _∼_ : {c₁ c₂ : U} → (f g : Fun c₁ c₂) → Set
  _∼_ {c₁ = c₁} {c₂ = c₂} f g =
    (eq : El c₁) →
    _≡_ {c = c₂} (app {c₁ = c₁} {c₂ = c₂} f eq) (app {c₁ = c₁} {c₂ = c₂} g eq)

  refl∼ : {c : U} → (f : Fun c c) →
          _∼_ {c₁ = c} {c₂ = c} f f
  refl∼ {c = c} f eq = refl≡ (app {c₁ = c} {c₂ = c} f eq)

  -- also need sym∼ and cong∼ and trans∼

  -- now we can prove that compose is associative:

  assoc-∘ : {c₁ c₂ c₃ c₄ : U}
            {f : Fun c₁ c₂} {g : Fun c₂ c₃} {h : Fun c₃ c₄} →
    _∼_ {c₁ = c₁} {c₄}
      (compose {c₁ = c₁} {c₂} {c₄} f (compose {c₁ = c₂} {c₃} {c₄} g h))
      (compose {c₁ = c₁} {c₃} {c₄} (compose {c₁ = c₁} {c₂} {c₃} f g) h)
  assoc-∘ = {!!}

  -- Equivalence

  record isequiv {c₁ c₂ : U}
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

  _≃_ : (c₁ c₂ : U) → Set
  _≃_ c₁ c₂ = Σ (Fun c₁ c₂) (isequiv {c₁ = c₁} {c₂ = c₂})

  -- Example level 1 equivalences

  id≃ : (c : U) → c ≃ c
  id≃ c = idF {c = c},
          mkisequiv
            (idF {c = c})
            (refl∼ {c = c} (idF {c = c}))
            (refl∼ {c = c} (idF {c = c}))

  -- the proofs below need trans∼ and inv∼, but then are straightforward.

  trans≃ : {c₁ c₂ c₃ : U} → (c₁ ≃ c₂) → (c₂ ≃ c₃) → (c₁ ≃ c₃)
  trans≃ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}
    (f , mkisequiv f⁻ α₁ β₁) (g , mkisequiv g⁻ α₂ β₂) =
    compose {c₁ = c₁} {c₂ = c₂} {c₃ = c₃} f g ,
    mkisequiv (compose {c₁ = c₃} {c₂ = c₂} {c₃ = c₁} g⁻ f⁻)
    (λ eq₁ → {!!})
    (λ eq₂ → {!!})

  -- Universe 1

  Univ : UNIVERSE
  Univ = record {
               U = A ⟷ B
             ; _⟷_ = _⇔_
             ; id⟷ = id⇔
             ; _◎⟷_ = _●_
             ; El = λ _ → A ≃₀ B
             ; Fun = Fun
             ; idF = λ {c} → idF {c = c}
             ; app = λ {c₁} {c₂} → app {c₁ = c₁} {c₂}
             ; _◎_ = λ {c₁} {c₂} {c₃} → flip (compose {c₁ = c₁} {c₂} {c₃})
             ; _≡_ = λ { {c} → _≡_ {c = c}}
             ; _∼_ = λ { {c₁} {c₂} → _∼_ {c₁ = c₁} {c₂ = c₂}}
             ; _≃_ = _≃_
             ; id≡ = refl≡
             ; sym≡ = {!!}
             ; trans≡ = trans≡
             ; cong≡ = cong≡
             ; refl∼ = refl∼
             ; sym∼ = {!!}
             ; trans∼ = {!!}
             ; id≃ = {!!}
             ; sym≃ = {!!}
             ; trans≃ = {!!}
             }

------------------------------------------------------------------------------
-- level 0-1 cross equivalences

module MOD0x1 where

  open MOD0
    using (_⟷_; id⟷; uniti₊r; unite₊r; _◎_; A⊎⊥≃A)
    renaming (U to U₀; _∼_ to _∼₀_;
              _≃_ to _≃₀_; id≃ to id≃₀; sym≃ to sym≃₀; trans≃ to trans≃₀)

  open MOD1
    using    ()
    renaming (U to U₁; El to El₁; _≡_ to _≡₁_; _≃_ to _≃₁_)

  -- We want to make sure that the level 1 codes are exactly the level 0
  -- equivalences. We will define a cross-level equivalence between them: that
  -- is univalence!

  -- Every code at level 1 does correspond to a level 0 equivalence
  -- Reverse direction is univalence; addressed below

  sound : {A B : U₀} → (c : U₁ A B) → El₁ A B c
  sound id⟷ = id≃₀
  sound uniti₊r = sym≃₀ MOD0.A⊎⊥≃A
  sound unite₊r = MOD0.A⊎⊥≃A
  sound (c₁ ◎ c₂) = trans≃₀ (sound c₁) (sound c₂)

  -- The two spaces in question are:
  -- A ≃₀ B in level 0 universe, and
  -- A ⟷ B in level 1 universe
  -- We need functions going in both directions that are inverses
  -- from A ⟷ B to A ≃₀ B we have the function sound in MOD1
  -- from A ≃₀ B to A ⟷ B we have the function complete below

  complete : {A B : U₀} → (A ≃₀ B) → (A ⟷ B)
  complete {A} {B} (MOD0.eq f g α β) = {!!}

  -- Now we need to require inverses

  record univalence {A B : U₀} : Set where
    field
      α : (c : A ⟷ B) → _≃₁_ A B (complete (sound c)) c
      β : (eq : A ≃₀ B) → Σ[ c ∈ A ⟷ B ] _≡₁_ A B {c = c} (sound (complete eq)) eq

{--
------------------------------------------------------------------------------
-- level 2 universe: codes for level 1 equivalences

module MOD2 where

  open MOD0
    using ()
    renaming (U to U₀)

  open MOD1
    using (_⟷_; id⟷; _◎_; !)
    renaming (app to app₁; _∼_ to _∼₁_;
              _≃_ to _≃₁_; id≃ to id≃₁; trans≃ to trans≃₁)

  -- Codes in level 2 for level 1 equivalences

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

  app : {A B : U₀} {c₁ c₂ : A ⟷ B} {α β : c₁ ⇔ c₂} → Fun α β → El α → El β
  app {A} {B} {c₁} {c₂} {α} {β} f eq = {!!}

  idF : {A B : U₀} {c₁ c₂ : A ⟷ B} {α : c₁ ⇔ c₂} → Fun α α
  idF = {!!}

  compose : {A B : U₀} {c₁ c₂ : A ⟷ B} {α β γ : c₁ ⇔ c₂} →
            (f : Fun α β) (g : Fun β γ) → Fun α γ
  compose = {!!}

  -- semantic notions on Univ₂:
  -- (1) when are two interpretations equivalent

  record _≡_ {A B : U₀} {c₁ c₂ : A ⟷ B} {α : c₁ ⇔ c₂}
              (eq₁ eq₂ : El α) : Set where
    open MOD1.isequiv (proj₂ eq₁) renaming (g to g₁)
    open MOD1.isequiv (proj₂ eq₂) renaming (g to g₂)
    field
      f≡ : _∼₁_ {c₁ = c₁} {c₂ = c₂} (proj₁ eq₁) (proj₁ eq₂)
      g≡ : _∼₁_ {c₁ = c₂} {c₂ = c₁} g₁ g₂

  _∼_ : {A B : U₀} {c₁ c₂ : A ⟷ B} {α β : c₁ ⇔ c₂} (f g : Fun α β) → Set
  _∼_ {α = α} {β = β} f g =
      (eq : El α) → _≡_ {α = β} (app f eq) (app g eq)

  record _≃_ {A B : U₀} {c₁ c₂ : A ⟷ B} (α β : c₁ ⇔ c₂) : Set where
    constructor eq
    field
      f : Fun α β
      g : Fun β α
      for : _∼_ {α = α} (compose g f) idF
      bck : _∼_ {α = β} (compose f g) idF

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
           ; app = {!!}
           ; _◎_ = {!!}
           ; _≡_ = {!!}
           ; _∼_ = {!!}
           ; _≃_ = {!!}
           ; id≡ = {!!}
           ; sym≡ = {!!}
           ; trans≡ = {!!}
           ; cong≡ = {!!}
           ; refl∼ = {!!}
           ; sym∼ = {!!}
           ; trans∼ = {!!}
           ; id≃ = {!!}
           ; sym≃ = {!!}
           ; trans≃ = {!!}
           }

------------------------------------------------------------------------------
-- level 1-2 cross equivalences

module MOD1x2 where

  open MOD0
    using    ()
    renaming (U to U₀)

  open MOD1
    using    (_⟷_)
    renaming (_≃_ to _≃₁_)

  open MOD2
    using    (_⇔_; sound)
    renaming (_≡_ to _≡₂_; _≃_ to _≃₂_)

  -- We want to make sure that the level 2 codes are exactly the level 1
  -- equivalences. We will define a cross-level equivalence between them: that
  -- is univalence!

  complete : {A B : U₀} {c₁ c₂ : A ⟷ B} → (c₁ ≃₁ c₂) → (c₁ ⇔ c₂)
  complete = {!!}

  record univalence {A B : U₀} {c₁ c₂ : A ⟷ B} : Set where
    field
      α : (α : c₁ ⇔ c₂) → complete (sound α) ≃₂ α
      β : (eq : c₁ ≃₁ c₂) → Σ[ α ∈ c₁ ⇔ c₂ ] _≡₂_ (sound (complete eq)) eq

------------------------------------------------------------------------------
-- Fractionals
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

  Univ₃ : UNIVERSE
  Univ₃ = record {
            U = U
          ; El = El
          ; Fun = Fun
          ; app = {!!}
          ; _◎_ = {!!}
          ; _≡_ = {!!}
          ; _∼_ = {!!}
          ; _≃_ = {!!}
          ; id≡ = {!!}
          ; sym≡ = {!!}
          ; trans≡ = {!!}
          ; cong≡ = {!!}
          ; refl∼ = {!!}
          ; sym∼ = {!!}
          ; trans∼ = {!!}
          ; id≃ = {!!}
          ; sym≃ = {!!}
          ; trans≃ = {!!}
          }

------------------------------------------------------------------------------
--}
