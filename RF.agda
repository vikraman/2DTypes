{-# OPTIONS --without-K #-}

module RF where

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
open import Relation.Binary.PropositionalEquality
open import Universe

------------------------------------------------------------------------------
-- Featherweight HoTT !
-- A mini language for programming with equivalences, identity types,
-- univalence, and higher inductive types (HITs).

------------------------------------------------------------------------------
-- Some general semantic notions

-- Homotopy

_∼_ : {A B : Set} → (f g : A → B) → Set
_∼_ {A} f g = (a : A) → f a ≡ g a

refl∼ : {A B : Set} → (f : A → B) → (f ∼ f)
refl∼ f a = refl -- (f a)

sym∼ : {A B : Set} {f g : A → B} → (f ∼ g) → (g ∼ f)
sym∼ H b = sym (H b)

trans∼ : {A B : Set} {f g h : A → B} → f ∼ g → g ∼ h → f ∼ h
trans∼ p₁ p₂ a = trans (p₁ a) (p₂ a)

∼○ : {A B C : Set} {f g : A → B} {h k : B → C} →
     (f ∼ g) → (h ∼ k) → ((h ○ f) ∼ (k ○ g))
∼○ {f = f} {g = g} {h = h} H₁ H₂ x = trans (cong h (H₁ x)) (H₂ (g x))

-- Equivalence given a particular function

record isequiv {A B : Set} (f : A → B) : Set where
  constructor mkisequiv
  field
    g : B → A
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

_≈_ : {A B : Set} {f : A → B} → isequiv f → isequiv f → Set
(mkisequiv g₁ _ _) ≈ (mkisequiv g₂ _ _) = g₁ ∼ g₂

refl≈ : {A B : Set} {f : A → B} → (eq : isequiv f) → eq ≈ eq
refl≈ (mkisequiv g _ _) = refl∼ g

sym≈ : {A B : Set} {f : A → B} {eq₁ eq₂ : isequiv f} →
       eq₁ ≈ eq₂ → eq₂ ≈ eq₁
sym≈ = sym∼

trans≈ : {A B : Set} {f : A → B} {eq₁ eq₂ eq₃ : isequiv f} →
       eq₁ ≈ eq₂ → eq₂ ≈ eq₃ → eq₁ ≈ eq₃
trans≈ = trans∼

-- Equivalence for some function

_≃_ : (A B : Set) → Set
A ≃ B = Σ[ f ∈ (A → B) ] (isequiv f)

refl≃ : {A : Set} → A ≃ A
refl≃ = id , mkisequiv id (λ _ → refl) (λ _ → refl)

sym≃ : {A B : Set} → (A ≃ B) → B ≃ A
sym≃ (f , mkisequiv g α β) = g , mkisequiv f β α


trans≃ : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
trans≃ (f , mkisequiv f⁻¹ fα fβ) (g , mkisequiv g⁻¹ gα gβ) =
  g ∘ f ,
  mkisequiv (f⁻¹ ∘ g⁻¹)
            (λ x → trans (cong g (fα (g⁻¹ x))) (gα x))
            (λ x → trans (cong f⁻¹ (gβ (f x))) (fβ x))

-- Higher homotopy between functions over isequiv

_≋_ : {A B : Set} {f g : A → B} (F G : isequiv f → isequiv g) → Set
_≋_ {f = f} {g = g} F G = (eq : isequiv f) → F eq ≈ G eq

refl≋ : {A B : Set} {f g : A → B} (F : isequiv f → isequiv g) → F ≋ F
refl≋ F eq = refl≈ (F eq)

sym≋ : {A B : Set} {f g : A → B} {F G : isequiv f → isequiv g} → F ≋ G → G ≋ F
sym≋ {g = g} {F} {G} E eq = sym≈ {f = g} {eq₁ = F eq} {eq₂ = G eq} (E eq)

trans≋ : {A B : Set} {f g : A → B} {F G H : isequiv f → isequiv g} →
         F ≋ G → G ≋ H → F ≋ H
trans≋ {g = g} {F} {G} {H} E₁ E₂ eq =
  trans≈ {f = g} {eq₁ = F eq} {eq₂ = G eq} {eq₃ = H eq} (E₁ eq) (E₂ eq)

------------------------------------------------------------------------------
-- Now we move to our language

-- The universe of small types which contains:
--   * the empty type
--   * the unit type
--   * coproducts
--   * products
--   * for any type A in this universe, and any two points a and b in A, the
--     identity type a ⊜ b. Note that this is recursive allowing A itself to be
--     an identity type. The identity types in this universe are all trivial
--     though.

module Universe₀ where

  infix 40 _⊜_
  infix 50 _⊕_
  infix 60 _⊗_

  -- Types: codes and interpretations

  data U : Set
  El : U → Set

  data U where
    𝟘 : U
    𝟙 : U
    _⊕_ : U → U → U
    _⊗_ : U → U → U
    _⊜_ : {A : U} → (a₁ a₂ : El A) → U

  El 𝟘 = ⊥
  El 𝟙 = ⊤
  El (A ⊕ B) = El A ⊎ El B
  El (A ⊗ B) = El A × El B
  El (a₁ ⊜ a₂) = a₁ ≡ a₂ -- identity type trivial in this universe

  TYPE : Universe _ _
  TYPE = record { U = U; El = El }

  -- Example

  module Refl-all-the-way where

    𝔹 : U
    𝔹 = 𝟙 ⊕ 𝟙

    _⊜𝔹_ : (a₁ a₂ : El 𝔹) → U
    _⊜𝔹_ = _⊜_

    x : El (inj₁ tt ⊜𝔹 inj₁ tt)
    x = refl

    -- y : El (inj₁ tt ⊜𝔹 inj₂ tt)
    -- ()

    z : El (_⊜_ {inj₁ tt ⊜𝔹 inj₁ tt} refl refl)
    z = refl

  -- Univalence

  module Univalence where

    -- we have no identity types between types yet; we cannot even state
    -- univalence at this point. If we were to try we would need
    -- idtoeqv : {A : U} {a b : El A} → El (_⊜_ {A} a b) → a ≃ b
    -- but a ≃ b is non-sensical as a and b are not types

  -- Some notions defined in U₀ that are needed to define U₁

  data _⟷_ : U → U → Set where
    refl⟷ : {A : U} → A ⟷ A
    uniti₊r : {A : U} → A ⟷ (A ⊕ 𝟘)
    unite₊r : {A : U} → A ⊕ 𝟘 ⟷ A
    swap₊ : {A B : U} → A ⊕ B ⟷ B ⊕ A
    assocl₊ : {A B C : U} → A ⊕ (B ⊕ C) ⟷ (A ⊕ B) ⊕ C
    assocr₊ : {A B C : U} → (A ⊕ B) ⊕ C ⟷ A ⊕ (B ⊕ C)
    _◎⟷_ : {A B C : U} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)
    _⊕_ : {A B C D : U} → (A ⟷ C) → (B ⟷ D) → (A ⊕ B ⟷ C ⊕ D)
    -- rest of rig axioms elided
    --
    -- new combinators for _⊜_; for each type former (including the identity
    -- type), we have a combinator that expresses the structure of paths at that
    -- type. The exact list of combinators will be confirmed in the proof of
    -- univalence in the next universe
    ⊜-⊤ :  tt ⊜ tt ⟷ 𝟙
    ⊜-⊕₁ : {A B : U} {a a' : El A} →
               (a ⊜ a' ⟷ 𝟙) → (_⊜_ {A ⊕ B} (inj₁ a) (inj₁ a') ⟷ 𝟙)
    ⊜-⊕₂ : {A B : U} {a : El A} {b : El B} →
               (inj₂ b ⊜ inj₁ a ⟷ 𝟘)
    ⊜-⊕₃ : {A B : U} {a : El A} {b : El B} →
               (inj₁ a ⊜ inj₂ b ⟷ 𝟘)
    ⊜-⊕₄ : {A B : U} {b b' : El B} →
               (b ⊜ b' ⟷ 𝟙) → (_⊜_ {A ⊕ B} (inj₂ b) (inj₂ b') ⟷ 𝟙)
    ⊜-⊗ : {A B : U} {a a' : El A} {b b' : El B} →
               (a ⊜ a' ⟷ 𝟙) → (b ⊜ b' ⟷ 𝟙) → ((a , b) ⊜ (a' , b') ⟷ 𝟙)
    ⊜-ID : {A : U} {a a' : El A} → (p q : El (a ⊜ a')) → (p ⊜ q ⟷ 𝟙)

  ! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
  ! unite₊r   = uniti₊r
  ! uniti₊r   = unite₊r
  ! swap₊     = swap₊
  ! assocl₊   = assocr₊
  ! assocr₊   = assocl₊
  ! refl⟷       = refl⟷
  ! (c₁ ◎⟷ c₂) = ! c₂ ◎⟷ ! c₁
  ! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
  ! _ = {!!}

  eval : {A B : U} → (A ⟷ B) → El A → El B
  eval refl⟷ = id
  eval uniti₊r a = inj₁ a
  eval unite₊r (inj₁ a) = a
  eval unite₊r (inj₂ ())
  eval swap₊ (inj₁ a) = inj₂ a
  eval swap₊ (inj₂ b) = inj₁ b
  eval assocl₊ (inj₁ a) = inj₁ (inj₁ a)
  eval assocl₊ (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
  eval assocl₊ (inj₂ (inj₂ c)) = inj₂ c
  eval assocr₊ (inj₁ (inj₁ a)) = inj₁ a
  eval assocr₊ (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
  eval assocr₊ (inj₂ c) = inj₂ (inj₂ c)
  eval (c₁ ◎⟷ c₂) = (eval c₂) ○ (eval c₁)
  eval (c₁ ⊕ c₂) (inj₁ a) = inj₁ (eval c₁ a)
  eval (c₁ ⊕ c₂) (inj₂ b) = inj₂ (eval c₂ b)
  eval ⊜-⊤ refl = tt
  eval (⊜-⊕₁ _) refl = tt
  eval ⊜-⊕₂ ()
  eval ⊜-⊕₃ ()
  eval (⊜-⊕₄ _) refl = tt
  eval (⊜-⊗ _ _) refl = tt
  eval (⊜-ID _ _) refl = tt

  evalB : {A B : U} → (A ⟷ B) → El B → El A
  evalB refl⟷ = id
  evalB uniti₊r (inj₁ a) = a
  evalB uniti₊r (inj₂ ())
  evalB unite₊r a = inj₁ a
  evalB swap₊ (inj₁ a) = inj₂ a
  evalB swap₊ (inj₂ b) = inj₁ b
  evalB assocl₊ (inj₁ (inj₁ a)) = inj₁ a
  evalB assocl₊ (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
  evalB assocl₊ (inj₂ c) = inj₂ (inj₂ c)
  evalB assocr₊ (inj₁ a) = inj₁ (inj₁ a)
  evalB assocr₊ (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
  evalB assocr₊ (inj₂ (inj₂ c)) = inj₂ c
  evalB (c₁ ◎⟷ c₂) = (evalB c₁) ○ (evalB c₂)
  evalB (c₁ ⊕ c₂) (inj₁ a) = inj₁ (evalB c₁ a)
  evalB (c₁ ⊕ c₂) (inj₂ b) = inj₂ (evalB c₂ b)
  evalB ⊜-⊤ tt = refl
  evalB (⊜-⊕₁ r) tt = cong inj₁ (evalB r tt)
  evalB ⊜-⊕₂ ()
  evalB ⊜-⊕₃ ()
  evalB (⊜-⊕₄ r) tt = cong inj₂ (evalB r tt)
  evalB (⊜-⊗ r₁ r₂) tt = cong₂ _,_ (evalB r₁ tt) (evalB r₂ tt)
  evalB (⊜-ID p q) tt = proof-irrelevance p q

  data _⇔_ : {A B : U} → (A ⟷ B) → (A ⟷ B) → Set where
    refl⇔ : {A B : U} {c : A ⟷ B} → (c ⇔ c)
    _●_ : {A B : U} {c₁ c₂ c₃ : A ⟷ B} → (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
    idl◎l : {A B : U} {c : A ⟷ B} → (refl⟷ ◎⟷ c) ⇔ c
    idl◎r : {A B : U} {c : A ⟷ B} → c ⇔ (refl⟷ ◎⟷ c)
    assocl⊕l : {A B C D E F : U} {c₁ : A ⟷ B} {c₂ : C ⟷ D} {c₃ : E ⟷ F} →
      ((c₁ ⊕ (c₂ ⊕ c₃)) ◎⟷ assocl₊) ⇔ (assocl₊ ◎⟷ ((c₁ ⊕ c₂) ⊕ c₃))
    assocl⊕r : {A B C D E F : U} {c₁ : A ⟷ B} {c₂ : C ⟷ D} {c₃ : E ⟷ F} →
      (assocl₊ ◎⟷ ((c₁ ⊕ c₂) ⊕ c₃)) ⇔ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎⟷ assocl₊)
    assocr⊕l : {A B C D E F : U} {c₁ : A ⟷ B} {c₂ : C ⟷ D} {c₃ : E ⟷ F} →
      (assocr₊ ◎⟷ (c₁ ⊕ (c₂ ⊕ c₃))) ⇔ (((c₁ ⊕ c₂) ⊕ c₃) ◎⟷ assocr₊)
    assocr⊕r : {A B C D E F : U} {c₁ : A ⟷ B} {c₂ : C ⟷ D} {c₃ : E ⟷ F} →
      (((c₁ ⊕ c₂) ⊕ c₃) ◎⟷ assocr₊) ⇔ (assocr₊ ◎⟷ (c₁ ⊕ (c₂ ⊕ c₃)))
    linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎⟷ ! c) ⇔ refl⟷
    linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → refl⟷ ⇔ (c ◎⟷ ! c)
    _⊡_  : {t₁ t₂ t₃ : U}
           {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₁ ⟷ t₂} {c₄ : t₂ ⟷ t₃} →
           (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎⟷ c₂) ⇔ (c₃ ◎⟷ c₄)
    -- rest of Laplaza axioms elided
    -- need new combinators for identity type

  2eval : {A B : U} {c₁ c₂ : A ⟷ B} → (c₁ ⇔ c₂) →
          isequiv (eval c₁) → isequiv (eval c₂)
  2eval = hom-eq ○ 2hom
    where
    2hom : {A B : U} {c₁ c₂ : A ⟷ B} → (c₁ ⇔ c₂) → eval c₁ ∼ eval c₂
    2hom {c₁ = c} refl⇔ = refl∼ (eval c)
    2hom (α ● β) = trans∼ (2hom α) (2hom β)
    2hom {c₂ = c} idl◎l = refl∼ (eval c)
    2hom {c₁ = c} idl◎r = refl∼ (eval c)
    2hom (assocl⊕l {c₁ = c₁}) (inj₁ a) = refl
    2hom (assocl⊕l {c₂ = c₂}) (inj₂ (inj₁ b)) = refl
    2hom (assocl⊕l {c₃ = c₃}) (inj₂ (inj₂ c)) = refl
    2hom (assocl⊕r {c₁ = c₁}) (inj₁ a) = refl
    2hom (assocl⊕r {c₂ = c₂}) (inj₂ (inj₁ b)) = refl
    2hom (assocl⊕r {c₃ = c₃}) (inj₂ (inj₂ c)) = refl
    2hom (assocr⊕l {c₁ = c₁}) (inj₁ (inj₁ a)) = refl
    2hom (assocr⊕l {c₂ = c₂}) (inj₁ (inj₂ b)) = refl
    2hom (assocr⊕l {c₃ = c₃}) (inj₂ c) = refl
    2hom (assocr⊕r {c₁ = c₁}) (inj₁ (inj₁ a)) = refl
    2hom (assocr⊕r {c₂ = c₂}) (inj₁ (inj₂ b)) = refl
    2hom (assocr⊕r {c₃ = c₃}) (inj₂ c) = refl
    2hom _ = {!!}

    hom-eq : {A B : Set} {f g : A → B} → (f ∼ g) → isequiv f → isequiv g
    hom-eq H (mkisequiv f⁻ α β) =
      mkisequiv f⁻
        (trans∼ (∼○ (refl∼ f⁻) (sym∼ H)) α)
        (trans∼ (∼○ (sym∼ H) (refl∼ f⁻)) β)

------------------------------------------------------------------------------
-- The next universe which contains:
--   * everything in Universe₀.U
--   * Universe₀.U itself
--   * identity types: for any type A in this universe, and any two points a and
--     b in A, the identity type a ⊜ b. Note that this is recursive allowing A
--     itself to be an identity type. The identity types in this universe are
--     non-trivial

module Universe₁ where

  open Universe₀
    using (_⟷_; _⇔_; eval; 2eval;
           𝟘; 𝟙; _⊕_;
           refl⟷; uniti₊r; unite₊r; swap₊; assocl₊; assocr₊; _◎⟷_;
           refl⇔; idl◎l; idl◎r; assocl⊕l; assocl⊕r; assocr⊕l; assocr⊕r;
           _●_; _⊡_; linv◎r)
    renaming (U to U₀; El to El₀; _⊜_ to _⊜₀_)

  data U : Set
  El : U → Set

  data U where
    ⇑ : U₀ → U
    U0 : U
    _⊜_ : {A : U} → (a₁ a₂ : El A) → U

  El (⇑ A) = El₀ A
  El U0 = U₀
  -- any identities lifted from U₀ are trivial
  El (_⊜_ {⇑ A} a b) = a ≡ b
  El (_⊜_ {_⊜_ {⇑ A} _ _} a b) = a ≡ b
  El (_⊜_ {_⊜_ {_⊜_ {⇑ A} _ _} _ _} a b) = a ≡ b
  -- identities between U₀ types are ⟷
  El (_⊜_ {U0} A B) = A ⟷ B
  -- identities between ⟷ are ⇔
  El (_⊜_ {_⊜_ {U0} A B} c₁ c₂) = c₁ ⇔ c₂
  -- identity of ⇔ is extensional
  El (_⊜_ {_⊜_ {_⊜_ {U0} A B} c₁ c₂} α β) = 2eval α ≋ 2eval β
  -- after that identities are trivial again
  El (_⊜_ {_⊜_ {_⊜_ {_⊜_ _ _} _ _} _ _} a b) = a ≡ b

  TYPE : Universe _ _
  TYPE = record { U = U; El = El }

  -- Examples

  module Examples where

    -- identities lifted from U₀

    𝔹 : U₀
    𝔹 = 𝟙 ⊕ 𝟙

    x : El (_⊜_ {⇑ 𝔹} (inj₁ tt) (inj₁ tt))
    x = refl

    y : El (_⊜_ {_⊜_ {⇑ 𝔹} (inj₁ tt) (inj₁ tt)} refl refl)
    y = refl

    z : El (_⊜_ {_⊜_ {_⊜_ {⇑ 𝔹} (inj₁ tt) (inj₁ tt)} refl refl} refl refl)
    z = refl

    -- identities between types; w₁ and w₂ are NOT equivalent but w₁, w₃, and w₄
    -- are all equivalent

    w₁ w₂ w₃ w₄ : El (_⊜_ {U0} (𝔹 ⊕ 𝟘) 𝔹)
    w₁ = unite₊r ◎⟷ refl⟷
    w₂ = unite₊r ◎⟷ swap₊
    w₃ = refl⟷ ◎⟷ (unite₊r ◎⟷ refl⟷)
    w₄ = unite₊r ◎⟷ (swap₊ ◎⟷ swap₊)

    -- identities between combinators

    α₁₃ α₁₃' : El (_⊜_ {_⊜_ {U0} (𝔹 ⊕ 𝟘) 𝔹} w₁ w₃)
    α₁₃ = idl◎r
    α₁₃' = idl◎r ● refl⇔

    α₁₄ : El (_⊜_ {_⊜_ {U0} (𝔹 ⊕ 𝟘) 𝔹} w₁ w₄)
    α₁₄ = refl⇔ ⊡ linv◎r

    -- identities between 2-combinators

    X Y : El (_⊜_ {_⊜_ {_⊜_ {U0} (𝔹 ⊕ 𝟘) 𝔹} w₁ w₃} α₁₃ α₁₃')
    X eq = refl≈ eq
    Y eq = refl≈ eq

    -- last level of identities

    L : El (_⊜_ {_⊜_ {_⊜_ {_⊜_ {U0} (𝔹 ⊕ 𝟘) 𝔹} w₁ w₃} α₁₃ α₁₃'} X Y)
    L = refl

  -- Univalence

  module Univalence where

    -- High-level structure: for each pair of types A and B such that A ⊜ B, we
    -- define a function idtoeqv and show it is an equivalence

    idtoeqv : {A B : U₀} → El (_⊜_ {U0} A B) → El₀ A ≃ El₀ B
    idtoeqv refl⟷ = refl≃
    idtoeqv uniti₊r = {!!} -- uniti+r≃
    idtoeqv unite₊r = {!!} -- sym≃ uniti+r≃
    idtoeqv (c₁ ◎⟷ c₂) = trans≃ (idtoeqv c₁) (idtoeqv c₂)
    idtoeqv assocl₊ = {!!} -- assocl₊≃
    idtoeqv assocr₊ = {!!} -- sym≃ assocl₊≃
    idtoeqv (c₁ ⊕ c₂) = {!!} -- (idtoeqv c₁) ⊕≃ (idtoeqv c₂)
    idtoeqv x = {!!}

    univalence : (A B : U₀) → Set
    univalence A B =  isequiv (idtoeqv {A} {B})

    -- univalence is NOT a postulate; we can prove it! The proof is essentially
    -- the completeness of ⟷ with respect to equivalence

    univalenceP : (A B : U₀) → univalence A B
    univalenceP A B = mkisequiv comp {!!} {!!}
      where comp : {A B : U₀} → (El₀ A ≃ El₀ B) → (A ⟷ B)
            comp {𝟘} {𝟘} _ = refl⟷
            comp {𝟙} {𝟙} _ = refl⟷
            comp {_} {_} eq = {!!}

    --------------------------------------------------------------------------
    -- then ⇔ is complete

    idtoeqv2 : {A B : U₀} {P Q : El (_⊜_ {U0} A B)} →
      El (_⊜_ {_⊜_ {U0} A B} P Q) → isequiv (eval P) ≃ isequiv (eval Q)
    idtoeqv2 refl⇔ = refl≃
    idtoeqv2 (α ● β) = trans≃ (idtoeqv2 α) (idtoeqv2 β)
    idtoeqv2 idl◎l = {!!}
    idtoeqv2 idl◎r = {!!}
    idtoeqv2 assocl⊕l = {!!}
    idtoeqv2 assocl⊕r = {!!}
    idtoeqv2 assocr⊕l = {!!}
    idtoeqv2 assocr⊕r = {!!}
    idtoeqv2 _ = {!!}

    univalence2 : {A B : U₀} (P Q : El (_⊜_ {U0} A B)) → Set
    univalence2 {A} {B} P Q =  isequiv (idtoeqv2 {A} {B} {P} {Q})

    univalence2P : {A B : U₀} (P Q : El (_⊜_ {U0} A B)) → univalence2 P Q
    univalence2P {A} {B} P Q = mkisequiv comp {!!} {!!}
      where comp : {A B : U₀} {c₁ c₂ : El (_⊜_ {U0} A B)} →
                   isequiv (eval c₁) ≃ isequiv (eval c₂) → c₁ ⇔ c₂
            comp {A} {B} {c₁} {c₂} eq = {!!}

    --------------------------------------------------------------------------
    -- idtoeqv3 as well

------------------------------------------------------------------------------
-- HITs; fractionals as  an example

------------------------------------------------------------------------------
-- Categorical semantics: We have a weak rig groupoid as shown in pi-dual
-- Here we show that we have a bicategory
-- https://en.wikipedia.org/wiki/Bicategory

module Cat where

  open Universe₀
    using (_⟷_; _⇔_; 2eval;
           refl⇔; _●_)
    renaming (U to U₀)

  -- Objects (also called 0-cells)

  0-cells : Set
  0-cells = U₀

  -- Morphisms with fixed source and target objects (also called 1-cells)

  1-cells : (A B : U₀) → Set
  1-cells A B = A ⟷ B

  -- Morphisms between morphisms with fixed source and target morphisms (which
  -- should have themselves the same source and the same target). These are also
  -- called 2-cells.

  2-cells : {A B : U₀} → (c₁ c₂ : A ⟷ B) → Set
  2-cells c₁ c₂ = c₁ ⇔ c₂

  -- Given two objects A and B there is a category whose objects are the 1-cells
  -- and morphisms are the 2-cells; the composition in this category is called
  -- vertical composition.

  𝔹 : (A B : U₀) → Category _ _ _
  𝔹 A B = record
    { Obj = A ⟷ B
    ; _⇒_ = _⇔_
    ; _≡_ = λ α β → 2eval α ≋ 2eval β
    ; id = refl⇔
    ; _∘_ = flip _●_ -- vertical composition
    ; assoc = λ {_} {_} {_} {_} {α} {β} {γ} → assoc {α = α} {β = β} {γ = γ}
    ; identityˡ = λ {_} {_} {α} → idl {α = α}
    ; identityʳ = λ {_} {_} {α} → idr {α = α}
    ; equiv = record { refl = λ {α} → refl≋ (2eval α) ;
                       sym = λ {α} {β} E → sym≋ {F = 2eval α} {G = 2eval β} E ;
                       trans =
                         λ {α} {β} {γ} E₁ E₂ →
                         trans≋ {F = 2eval α} {G = 2eval β} {H = 2eval γ} E₁ E₂ }
    ; ∘-resp-≡ = λ {_} {_} {_} {α} {β} {γ} {δ} E₁ E₂ →
                 resp {α = α} {β = β} {γ = γ} {δ = δ} E₁ E₂
    }
    where
    idl : {A B : U₀} {c₁ c₂ : A ⟷ B} {α : c₁ ⇔ c₂} → 2eval (α ● refl⇔) ≋ 2eval α
    idl (mkisequiv g p q) b = refl

    idr : {A B : U₀} {c₁ c₂ : A ⟷ B} {α : c₁ ⇔ c₂} → 2eval (refl⇔ ● α) ≋ 2eval α
    idr (mkisequiv g p q) b = refl

    assoc : {A B : U₀} {c₁ c₂ c₃ c₄ : A ⟷ B}
          {α : c₁ ⇔ c₂} {β : c₂ ⇔ c₃} {γ : c₃ ⇔ c₄} →
          2eval (α ● (β ● γ)) ≋ 2eval ((α ● β) ● γ)
    assoc (mkisequiv g p q) b = refl

    resp : {A B : U₀} {c₁ c₂ c₃ : A ⟷ B} {α β : c₂ ⇔ c₃} {γ δ : c₁ ⇔ c₂} →
         2eval α ≋ 2eval β → 2eval γ ≋ 2eval δ →
         2eval (γ ● α) ≋ 2eval (δ ● β)
    resp E₁ E₂ (mkisequiv g p q) b = refl

  -- given three objects A, B, and C there is a bifunctor * : 𝔹(B,C) × 𝔹(A,B) →
  -- 𝔹(A,C) called horizontal composition; the horizontal composition is required
  -- to be associative up to natural isomorphism between h*(g*f) and (h*g)*f

  -- TODO

  -- coherence conditions !!!

  -- TODO

------------------------------------------------------------------------------
