{-# OPTIONS --without-K #-}

module R3 where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Function renaming (_∘′_ to _○_)
open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Product as C
open import Categories.Groupoid.Product as G
open import Categories.Agda using (Sets)
open import Categories.Functor using (Functor; Full; Faithful; EssentiallySurjective)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Nat hiding (_⊔_; _≟_)
open import Data.Integer as ℤ hiding (_⊔_; _≟_)
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_)
open import Relation.Binary using (Decidable)
open import Relation.Nullary
open import Equiv

------------------------------------------------------------------------------
-- level 0 syntax and interpretation

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


  -- The morphisms are trivial in that they exist
  -- only when types A and B are identical

  Fun : (A B : U) → Set
  Fun = _==_

  SynCat0 : Category _ _ _
  SynCat0 = record
    { Obj = U
    ; _⇒_ = Fun
    ; _≡_ = _==_
    ; id = refl
    ; _∘_ = flip trans
    ; assoc = {!!}
    ; identityˡ = {!!}
    ; identityʳ = {!!}
    ; equiv = isEquivalence
    ; ∘-resp-≡ = λ { {_} {_} {f} refl refl → refl}
    }

  Sem : Functor (SynCat0) (Sets lzero)
  Sem = record
    { F₀ = El
    ; F₁ = λ { {A} refl → id}
    ; identity = refl
    ; homomorphism = λ { {f = refl} {refl} → refl}
    ; F-resp-≡ = λ { {A} {F = refl} {refl} refl → refl}
    }

  Sem-is-Faithful : Faithful Sem
  Sem-is-Faithful f g _ = proof-irrelevance f g

  -- Sem is definitely NOT essentially surjective.
  -- It might be Full, but the proof seems non-trivial

------------------------------------------------------------------------------
-- level 1 universe: codes correspond to equivalences

-- We actually need to refine two things in parallel:
-- 1. what counts as 'equivalent' codes in U
-- 2. what counts as 'equivalent' types
--
-- We first deal with equivalent types, as these are independent
-- of codes, so this is all defined in module Equiv, and the
-- examples are in TypeEquiv


module MOD1 where
  open import TypeEquiv as TE

  open MOD0
    using    (𝟘; 𝟙; _⊕_; _⊗_)
    renaming (U to U₀; El to El₀)

  -- Codes in level 1 for level 1 equivalences

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

  -- Every code at level 1 does correspond to a set equivalence
  -- Reverse direction is univalence; addressed below

  Fun : {A B : U₀} → (c : A ⟷ B) → El₀ A ≃ El₀ B
  Fun id⟷ = id≃
  Fun uniti₊r = TE.uniti₊′equiv
  Fun unite₊r = TE.unite₊′equiv
  Fun (c₁ ◎ c₂) = (Fun c₂) ● (Fun c₁)

  SynCat1 : Category _ _ _
  SynCat1 = record
    { Obj = U₀
    ; _⇒_ = _⟷_
    ; _≡_ = _==_ -- boring equality, but not trivial!
    ; id = id⟷
    ; _∘_ = λ y⟷z x⟷y → x⟷y ◎ y⟷z
    ; assoc = {!!}
    ; identityˡ = {!!}
    ; identityʳ = {!!}
    ; equiv = isEquivalence
    ; ∘-resp-≡ = λ { {f = f} refl refl → refl }
    }

  -- this is not really the semantics we want, but we can get it nevertheless:
  Sem : Functor SynCat1 (Sets lzero)
  Sem = record
    { F₀ = El₀
    ; F₁ = λ c → _≃_.f (Fun c)
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≡ = λ { {F = F} refl → refl}
    }

  -- The semantics we want uses this other category:
  ESets : Category _ _ _
  ESets = record
    { Obj = Set lzero
    ; _⇒_ = _≃_
    ; _≡_ = _==_
    ; id = id≃
    ; _∘_ = _●_
    ; assoc = {!!}
    ; identityˡ = {!!}
    ; identityʳ = {!!}
    ; equiv = record { refl = refl ; sym = sym ; trans = trans }
    ; ∘-resp-≡ = λ { {f = f} refl refl → refl}
    }

  -- The semantics we want!
  SemGood : Functor SynCat1 ESets
  SemGood = record
    { F₀ = El₀
    ; F₁ = Fun
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≡ = λ { {F = F} refl → refl}
    }

{-

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
  complete {A} {B} (MOD0.eq f g α β) = {!!}

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
-}
------------------------------------------------------------------------------
