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

------------------------------------------------------------------------------
-- Note that univalence, which used to be in here, cannot be phrased
-- properly until level 2.  This is correct and expected.
-- completeness, on the other hand, does belong here.

module MOD0x1 where

  open MOD0
    using    ()
    renaming (U to U₀; El to El₀)

  open MOD1
    using    (_⟷_; id⟷; uniti₊r; unite₊r; _◎_; Fun)

  -- We want to make sure that the level 1 codes are exactly the
  -- equivalences.

  complete : {A B : U₀} → (El₀ A ≃ El₀ B) → (A ⟷ B)
  complete {A} {B} (qeq f g α β) = {!!}

------------------------------------------------------------------------------
-- level 2 universe: codes for equivalences between level 1 equivalences

module MOD2 where
  open import EquivEquiv

  open MOD0
    using ()
    renaming (U to U₀; El to El₀)

  open MOD1
    using (_⟷_; id⟷; _◎_; !; Fun)

  open MOD0x1
    using (complete)

  -- Codes in level 2 for level 1 equivalences
  data _⇔_ : {A B : U₀} → (A ⟷ B) → (A ⟷ B) → Set where
    id⇔ : ∀ {A B} {c : A ⟷ B} → c ⇔ c
    _◍_  : ∀ {A B} {c₁ c₂ c₃ : A ⟷ B} → (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)

  2! : {A B : U₀} {c₁ c₂ : A ⟷ B} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
  2! id⇔ = id⇔
  2! (α ◍ β) = (2! β) ◍ (2! α)

  -- Every code at level 2 does correspond to an equivalence of equivalences
  -- Reverse direction is univalence; addressed below

  sound : {A B : U₀} {c₁ c₂ : A ⟷ B} → (α : c₁ ⇔ c₂) → Fun c₁ ≋ Fun c₂
  sound {c₁ = c} {c₂ = .c} id⇔ = id≋
  sound (α₁ ◍ α₂) = trans≋ (sound α₁) (sound α₂)

  -- univalence for level 2: relates level 1 equivalences with level 2 codes for
  -- these equivalences

  record univalence {A B : U₀} : Set where
    field
      α : (c : A ⟷ B) → complete (Fun c) ⇔ c
      β : (eq : El₀ A ≃ El₀ B) → Fun (complete eq) ≋ eq

  SynCat2 : Category _ _ _
  SynCat2 = record
    { Obj = U₀
    ; _⇒_ = _⟷_
    ; _≡_ = _⇔_
    ; id = id⟷
    ; _∘_ = λ x⟷y y⟷z → y⟷z ◎ x⟷y
    ; assoc = {!!}
    ; identityˡ = {!!}
    ; identityʳ = {!!}
    ; equiv = {!!}
    ; ∘-resp-≡ = {!!}
    }

  WeakSets : Category _ _ _
  WeakSets = record
    { Obj = Set
    ; _⇒_ = _≃_
    ; _≡_ = _≋_
    ; id = id≃
    ; _∘_ = _●_
    ; assoc = {!!}
    ; identityˡ = lid≋
    ; identityʳ = rid≋
    ; equiv = record { refl = id≋ ; sym = sym≋ ; trans = trans≋ }
    ; ∘-resp-≡ = {!!}
    }

  Sem : Functor SynCat2 WeakSets
  Sem = record
    { F₀ = El₀
    ; F₁ = Fun
    ; identity = id≋
    ; homomorphism = id≋
    ; F-resp-≡ = sound
    }

  open import Categories.Bicategory
  open import Categories.Bifunctor
  open import Categories.NaturalIsomorphism

  -- a few helper functions, to make the actual definition below readable
  ⟷Cat : U₀ → U₀ → Category _ _ _
  ⟷Cat A B = record
    { Obj = A ⟷ B
    ; _⇒_ = _⇔_
    ; _≡_ = λ _ _ → ⊤ -- because we don't have anything else available
    ; id = id⇔
    ; _∘_ = λ c₂⇔c₃ c₁⇔c₂ → c₁⇔c₂ ◍ c₂⇔c₃
    ; assoc = tt
    ; identityˡ = tt
    ; identityʳ = tt
    ; equiv = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
    ; ∘-resp-≡ = λ _ _ → tt
    }

  ⟷BiFunc : {A B C : U₀} → Bifunctor (⟷Cat B C) (⟷Cat A B) (⟷Cat A C)
  ⟷BiFunc = record
    { F₀ = λ { (b⟷c , a⟷b) → a⟷b ◎ b⟷c }
    ; F₁ = λ { {(c₁ , c₂)} {(c₃ , c₄)} (c₁⇔c₃ , c₂⇔c₄) → {!!} }
    ; identity = tt
    ; homomorphism = tt
    ; F-resp-≡ = λ _ → tt
    }

  SynWeakBicat : Bicategory _ _ _ _
  SynWeakBicat = record
    { Obj = U₀
    ; _⇒_ = ⟷Cat
    ; id = record
             { F₀ = λ _ → id⟷
             ; F₁ = λ _ → id⇔
             ; identity = tt
             ; homomorphism = tt
             ; F-resp-≡ = λ _ → tt
             }
    ; —∘— = ⟷BiFunc
    ; λᵤ = record { F⇒G = record { η = λ { (_ , c₁) → {!!}} ; commute = {!!} }
                  ; F⇐G = record { η = λ {(_ , c₁) → {!!}} ; commute = {!!} }
                  ; iso = λ X → record { isoˡ = tt ; isoʳ = tt } }
    ; ρᵤ = record { F⇒G = record { η = λ {(c₁ , _) → {!!}} ; commute = {!!} }
                  ; F⇐G = record { η = λ {(c₁ , _) → {!!}} ; commute = {!!} }
                  ; iso = λ X → record { isoˡ = tt ; isoʳ = tt } }
    ; α = record { F⇒G = record { η = λ {(c₁ , c₂ , c₃) → {!!}} ; commute = {!!} }
                 ; F⇐G = record { η = λ {(c₁ , c₂ , c₃) → {!!}} ; commute = {!!} }
                 ; iso = λ X → record { isoˡ = tt ; isoʳ = tt } }
    ; triangle = λ _ _ → tt
    ; pentagon = λ _ _ _ _ → tt
    }

{-
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
