{-# OPTIONS --without-K #-}

module R where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Universe using (Universe; Indexed-universe)
open import Function renaming (_∘_ to _○_)
open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Product as C
open import Categories.Groupoid.Product as G
open import Level renaming (zero to lzero)
open import Data.Nat
open import Data.Integer as ℤ

-- infix 4 _≃_
-- infix 4 _≋_
-- infix 40 _^_
-- infixr 50 _◎_
-- infix 50 _⊠_
-- infixr 60 _●_

------------------------------------------------------------------------------
-- Featherweight HoTT !

-- Each universe has:
--   * code U for types
--   * an interpretation El of these codes as semantics
--   * a semantic notion of equivalence on the interpretations
--   * possibly other semantic notions like fractional groupoids

-- The first universe (level 0) is fairly obvious

-- Once we have that level 0 universe, we can define a new universe (level 1)
-- whose codes are the equivalences at level 0. As outlined above, we then
-- define a notion of equivalence at level 1 that relates the level 0
-- equivalences.

-- We can now define a level 2 universe whose codes are the level 1
-- equivalences. We then repeat and define a notion of eqiuvalence at level 2
-- that relates the level 1 equivalences.

------------------------------------------------------------------------------
-- level 0 universe

module UNIV0 where

  infix 50 _⊕_
  infix 60 _⊗_

  data U₀ : Set where
    𝟘   : U₀
    𝟙   : U₀
    _⊕_ : U₀ → U₀ → U₀
    _⊗_ : U₀ → U₀ → U₀

  El₀ : U₀ → Set
  El₀ 𝟘         = ⊥
  El₀ 𝟙         = ⊤
  El₀ (t₁ ⊕ t₂) = El₀ t₁ ⊎ El₀ t₂
  El₀ (t₁ ⊗ t₂) = El₀ t₁ × El₀ t₂

  Univ₀ : Universe _ _
  Univ₀ = record { U = U₀ ; El = El₀ }

  -- semantic notions on Univ₀:
  -- when are interpretations equivalent

  data _≡₀_ {A : U₀} : (a b : El₀ A) → Set where
    refl₀ : (a : El₀ A) → (a ≡₀ a)

  _∼₀_ : {A B : U₀} → (f g : El₀ A → El₀ B) → Set
  _∼₀_ {A} {B} f g = (x : El₀ A) → f x ≡₀ g x

  record isequiv₀ {A B : U₀} (f : El₀ A → El₀ B) : Set where
    constructor mkisequiv₀
    field
      g : El₀ B → El₀ A
      α : (f ○ g) ∼₀ id
      β : (g ○ f) ∼₀ id

  _≃₀_ : (A B : U₀) → Set
  A ≃₀ B = Σ (El₀ A → El₀ B) isequiv₀

  -- example of actual equivalence of interpretations

  A⊎⊥≃A : {A : U₀} → A ⊕ 𝟘 ≃₀ A
  A⊎⊥≃A {A} = f , mkisequiv₀ g α β
    where
      f : (El₀ A ⊎ ⊥) → El₀ A
      f (inj₁ a) = a
      f (inj₂ ())

      g : El₀ A → (El₀ A ⊎ ⊥)
      g a = inj₁ a

      α : (f ○ g) ∼₀ id
      α a = refl₀ a

      β : (g ○ f) ∼₀ id
      β (inj₁ a) = refl₀ (inj₁ a)
      β (inj₂ ())

  idequiv : {A : U₀} → A ≃₀ A
  idequiv = (id , mkisequiv₀ id refl₀ refl₀)

  transequiv : {A B C : U₀} → A ≃₀ B → B ≃₀ C → A ≃₀ C
  transequiv (f , mkisequiv₀ f⁻ α₁ β₁) (g , mkisequiv₀ g⁻ α₂ β₂) =
    g ○ f , mkisequiv₀ (f⁻ ○ g⁻) {!!} {!!}

------------------------------------------------------------------------------
-- level 1 universe: codes for level 0 semantic equivalence

open UNIV0

module UNIV1 where

  data _⟷_ : U₀ → U₀ → Set where
    id⟷ : {A : U₀} → A ⟷ A
    uniti₊r : {A : U₀} → A ⟷ (A ⊕ 𝟘)
    unite₊r : {A : U₀} → A ⊕ 𝟘 ⟷ A
    _◎_ :  {A B C : U₀} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)
    -- elided

  ! : {A B : U₀} → (A ⟷ B) → (B ⟷ A)
  ! unite₊r = uniti₊r
  ! uniti₊r = unite₊r
  ! id⟷ = id⟷
  ! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁

  Univ₁ : Indexed-universe _ _ _
  Univ₁ = record {
             I = U₀ × U₀
           ; U = λ { (A , B) → A ⟷ B }
           ; El = λ { { (A , B) } c → A ≃₀ B }
           }

  open Indexed-universe Univ₁ renaming (El to EL1)

  El₁ : {A B : U₀} → (c : A ⟷ B) → EL1 c
  El₁ id⟷ = {!!}
  El₁ uniti₊r = {!!}
  El₁ unite₊r = A⊎⊥≃A
  El₁ (c₁ ◎ c₂) = {!!}

  -- semantic notions on Univ₁:
  -- when are two interpretations equivalent

  record _≡₁_ {A B : U₀} {c₁ c₂ : A ⟷ B}
              (eq₁ : EL1 c₁) (eq₂ : EL1 c₂)  : Set where
    open isequiv₀ (proj₂ eq₁) renaming (g to g₁)
    open isequiv₀ (proj₂ eq₂) renaming (g to g₂)
    field
      f≡ : proj₁ eq₁ ∼₀ proj₁ eq₂
      g≡ : g₁ ∼₀ g₂

  _∼₁_ : {A B C D : U₀} {c₁ : A ⟷ B} {c₂ : C ⟷ D} →
         (f g : EL1 c₁ → EL1 c₂) → Set
  _∼₁_ {c₁ = c₁} {c₂ = c₂} f g =
         (eq₁ : EL1 c₁) → _≡₁_ {c₁ = c₂} {c₂ = c₂} (f eq₁) (g eq₁)

  record isequiv₁ {A B C D : U₀} {c₁ : A ⟷ B} {c₂ : C ⟷ D}
                  (f : EL1 c₁ → EL1 c₂) : Set where
    constructor mkisequiv₁
    field
      g : EL1 c₂ → EL1 c₁
      α : _∼₁_ {c₁ = c₂} {c₂ = c₂} (f ○ g) id
      β : _∼₁_ {c₁ = c₁} {c₂ = c₁} (g ○ f) id

  _≃₁_ : {A B C D : U₀} {c₁ : A ⟷ B} {c₂ : C ⟷ D} → Set
  _≃₁_ {c₁ = c₁} {c₂ = c₂} =
    Σ (EL1 c₁ → EL1 c₂) (isequiv₁ {c₁ = c₁} {c₂ = c₂})

------------------------------------------------------------------------------
{--

-- codes for equivalences of equivalences

data _⇔_ : {t₁ t₂ : U₀} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  id⇔ : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → c ⇔ c
  _●_  : ∀ {t₁ t₂} {c₁ c₂ c₃ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)

data U₀/ : Set where
  # : {t : U₀} → (t ⟷ t) → U₀/
  1/# : {t : U₀} → (c : t ⟷ t) → U₀/
  _⊠_ : U₀/ → U₀/ → U₀/

2! : {t₁ t₂ : U₀} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
2! id⇔ = id⇔
2! (α ● β) = (2! β) ● (2! α)

U₀/-univ : Universe _ _
U₀/-univ = record {
            U = U₀/
          ; El = λ t/ → Σ[ C ∈ Category lzero lzero lzero ] (Groupoid C)
          }

TT-univ : Indexed-universe _ _ _
TT-univ = record {
            I = Σ[ t₁ ∈ U₀ ] Σ[ t₂ ∈ U₀ ] (t₁ ⟷ t₂) × (t₁ ⟷ t₂)
          ; U = λ { (t₁ , t₂ , c₁ , c₂) → c₁ ⇔ c₂ }
          ; El = λ { {(t₁ , t₂ , c₁ , c₂)} α →
                   _≃₁_ {Universe.El Univ₀ t₁}
                        {Universe.El Univ₀ t₂}
                        {Universe.El Univ₀ t₁}
                        {Universe.El Univ₀ t₂}
                   (Indexed-universe.El T-univ {(t₁ , t₂)} c₁)
                   (Indexed-universe.El T-univ {(t₁ , t₂)} c₂) }
          }

⟦_⟧₁ : {t₁ t₂ : U₀} {c₁ c₂ : t₁ ⟷ t₂} → (α : c₁ ⇔ c₂) →
      Indexed-universe.El TT-univ {(t₁ , t₂ , c₁ , c₂)} α
⟦ id⇔ ⟧₁ = id ,
           mkisequiv₁
             id
             (λ { (f , mkisequiv g α h β) →
                eq (λ x → refl (f x))
                   (λ x → refl (g x)) })
             id
             ((λ { (f , mkisequiv g α h β) →
               eq (λ x → refl (f x))
                  (λ x → refl (g x))}))
⟦ α₁ ● α₂ ⟧₁ = {!!}

-- equivalences at level 2

record _≋₂_ {A B C D : Set} (e₁ e₂ : A ≃₁ B) : Set where
  constructor eq₂
  open isequiv₁ (proj₂ e₁) renaming (g to g₁)
  open isequiv₁ (proj₂ e₂) renaming (g to g₂)
  field
    f≡ : proj₁ e₁ ∼₁ proj₁ e₂
    g≡ : g₁ ∼₁ g₂

-- homotopy at level 2

_∼₂_ : {A B C D : Set} → (f g : A ≃₁ B → C ≃₁ D) → Set
_∼₂_ {A} {B} {C} {D} f g = (eq : A ≃₁ B) → f eq ≋₂ g eq

-- equivalences at level 2

record isequiv₂ {A B C D : Set} (f : A ≃₁ B → C ≃₁ D) : Set where
  constructor mkisequiv₂
  field
    g : C ≃₁ D → A ≃₁ B
    α : (f ○ g) ∼₂ id
    h : C ≃₁ D → A ≃₁ B
    β : (h ○ f) ∼₂ id

_≃₂_ : {A B C D : Set} → (A≃₁B C≃₁D : Set) → Set
_≃₂_ {A} {B} {C} {D} A≃₁B C≃₁D = Σ (A ≃₁ B → C ≃₁ D) isequiv₂


-- fractionals; refers to ⇔ so must live in this universe

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

⟦_⟧/ : (t/ : U₀/) → Universe.El U₀/-univ t/
⟦ # c ⟧/ = _ , orderG c
⟦ 1/# c ⟧/ = {!!}
⟦ T₁ ⊠ T₂ ⟧/ with ⟦ T₁ ⟧/ | ⟦ T₂ ⟧/
... | (C₁ , G₁) | (C₂ , G₂) = C.Product C₁ C₂ , G.Product G₁ G₂

-- once we complete the entire set of _⟷_ we will have the following situation:
-- the space A ⊕ A ≃ A ⊕ A contains the following elements:
-- id≃
-- swap≃
-- these two elements should not be identified
-- in the world of codes these elements are represented by different codes
-- id⟷ and swap₊
-- the relation ⇔ tells us which codes can be identified and it does NOT identify
-- id⟷ and swap₊

------------------------------------------------------------------------------
-- fractionals


------------------------------------------------------------------------------
--}
