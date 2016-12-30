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
    -- equivalence relation on points in a space
    _≡_ : {A : U} (a b : El A) → Set
    -- equivalence of functions from spaces to spaces
    _∼_ : {A B : U} (f g : El A → El B) → Set
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

  -- Identity

  data _≡_ {A : U} : (a b : El A) → Set where
    refl : (a : El A) → (a ≡ a)

  sym≡ : {A : U} {a b : El A} → a ≡ b → b ≡ a
  sym≡ (refl a) = refl a

  trans≡ : {A : U} {a b c : El A} → a ≡ b → b ≡ c → a ≡ c
  trans≡ (refl a) (refl .a) = refl a

  cong≡ : {A B : U} {a b : El A} → (f : El A → El B) (p : a ≡ b) →
          f a ≡ f b
  cong≡ f (refl a) = refl (f a)

  -- Homotopy

  _∼_ : {A B : U} → (f g : El A → El B) → Set
  _∼_ {A} {B} f g = (a : El A) → f a ≡ g a

  refl∼ : {A B : U} → (f : El A → El B) → (f ∼ f)
  refl∼ f a = refl (f a)

  trans∼ : {A B : U} {f g h : El A → El B} → f ∼ g → g ∼ h → f ∼ h
  trans∼ p₁ p₂ a = trans≡ (p₁ a) (p₂ a)

  -- Equivalence

  record isequiv {A B : U} (f : El A → El B) : Set where
    constructor mkisequiv
    field
      g : El B → El A
      α : (f ○ g) ∼ id
      β : (g ○ f) ∼ id

  _≃_ : (A B : U) → Set
  A ≃ B = Σ (El A → El B) isequiv

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
         ; _≡_ = _≡_
         ; _∼_ = _∼_
         ; _≃_ = _≃_
         }

------------------------------------------------------------------------------
-- level 1 universe: codes correspond to level 0 equivalences

module MOD1 where

  open MOD0
    using    (𝟘; 𝟙; _⊕_; _⊗_)
    renaming (U to U₀; _∼_ to _∼₀_; _≃_ to _≃₀_)

  -- Codes for level 0 equivalences

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

  cong≡ : {A B C D : U₀} {c₁ : A ⟷ B} {c₂ : C ⟷ D} {eq₁ eq₂ : El c₁} →
    (f : El c₁ → El c₂) → _≡_ {c = c₁} eq₁ eq₂ → _≡_ {c = c₂} (f eq₁) (f eq₂)
  cong≡ {eq₁ = eq₁} {eq₂ = eq₂} f (record { f≡ = f≡ ; g≡ = g≡ }) =
    let (hr₁ , MOD0.mkisequiv gr₁ αr₁ βr₁) = f eq₁
        (hr₂ , MOD0.mkisequiv gr₂ αr₂ βr₂) = f eq₂
    in record {
         f≡ = λ x → MOD0.cong≡ {!!} (f≡ {!!})
       ; g≡ = λ x → MOD0.cong≡ {!!} (g≡ {!!})
       }

  -- Homotopy

  _∼_ : {A B : U₀} {c₁ c₂ : A ⟷ B} → (f g : El c₁ → El c₂) → Set
  _∼_ {c₁ = c₁} {c₂ = c₂} f g = (eq : El c₁) → _≡_ {c = c₂} (f eq) (g eq)

  refl∼ : {A B : U₀} {c : A ⟷ B} → (f : El c → El c) →
          _∼_ {c₁ = c} {c₂ = c} f f
  refl∼ f eq = refl≡ (f eq)

  -- Equivalence

  record isequiv {A B : U₀} {c₁ c₂ : A ⟷ B}
         (f : El c₁ → El c₂) : Set where
    constructor mkisequiv
    field
      g : El c₂ → El c₁
      α : _∼_ {c₁ = c₂} {c₂ = c₂} (f ○ g) id
      β : _∼_ {c₁ = c₁} {c₂ = c₁} (g ○ f) id

  _≃_ : {A B : U₀} → (c₁ c₂ : A ⟷ B) → Set
  _≃_ {A} {B} c₁ c₂ = Σ (El c₁ → El c₂) (isequiv {c₁ = c₁} {c₂ = c₂})

  -- Example level 1 equivalences

  id≃ : {A B : U₀} → (c : A ⟷ B) → c ≃ c
  id≃ c = id ,
          mkisequiv
            id
            (refl∼ {c = c} id)
            (refl∼ {c = c} id)

  trans≃ : {A B : U₀} {c₁ c₂ c₃ : A ⟷ B} → (c₁ ≃ c₂) → (c₂ ≃ c₃) → (c₁ ≃ c₃)
  trans≃ {c₁ = c₁} {c₃ = c₃} (f , mkisequiv f⁻ α₁ β₁) (g , mkisequiv g⁻ α₂ β₂) =
    g ○ f , mkisequiv (f⁻ ○ g⁻) α β
      where α : (x : El c₃) → (g (f (f⁻ (g⁻ x)))) ≡ x
            α x = trans≡ (cong≡ g (α₁ (g⁻ x))) (α₂ x)
            β : (x : El c₁) → (f⁻ (g⁻ (g (f x)))) ≡ x
            β x = trans≡ (cong≡ f⁻ (β₂ (f x))) (β₁ x)

  -- Universe 1

  Univ : (A B : U₀) → UNIVERSE
  Univ A B = record {
               U = A ⟷ B
             ; El = λ _ → A ≃₀ B
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
    using (_⟷_)
    renaming (_≃_ to _≃₁_; id≃ to id≃₁; trans≃ to trans≃₁)

  -- Codes for level 1 equivalences

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

  -- Universe 2

  Univ : {A B : U₀} (c₁ c₂ : A ⟷ B) → UNIVERSE
  Univ c₁ c₂ = record {
             U = c₁ ⇔ c₂
           ; El = {!!}
           ; _≡_ = {!!}
           ; _∼_ = {!!}
           ; _≃_ = {!!}
           }

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

------------------------------------------------------------------------------
-- fractionals
-- level 3 universe: codes for level 2 quotients

open UNIV2

module UNIV3 where

  data U₃ : Set where
    # : {t : U₀} → (t ⟷ t) → U₃
    1/# : {t : U₀} → (c : t ⟷ t) → U₃
    _⊠_ : U₃ → U₃ → U₃

  Univ₃ : Universe _ _
  Univ₃ = record {
              U = U₃
            ; El = λ A → Σ[ C ∈ Category lzero lzero lzero ] (Groupoid C)
            }

  open Universe.Universe Univ₃ renaming (El to EL3)

  El₃ : (A : U₃) → EL3 A
  El₃ (# c) = _ , orderG c
  El₃ (1/# c) = {!!}
  El₃ (A ⊠ B) with El₃ A | El₃ B
  ... | (C₁ , G₁) | (C₂ , G₂) = C.Product C₁ C₂ , G.Product G₁ G₂

  -- semantic notions on Univ₃
  -- ??

------------------------------------------------------------------------------
--}
