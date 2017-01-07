{-# OPTIONS --without-K #-}

module B where

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product hiding (swap)
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
--   * the type of booleans
--   * for any type A in this universe, and any two points a and b in A, the
--     identity type a ⊜ b. Note that this is recursive allowing A itself to be
--     an identity type. The identity types in this universe are all trivial
--     though.

module Universe₀ where

  infix 40 _⊜_

  -- Types: codes and interpretations

  data U : Set
  El : U → Set

  data U where
    𝟘 : U
    𝟙 : U
    𝔹 : U
    _⊜_ : {A : U} → (a₁ a₂ : El A) → U

  El 𝟘 = ⊥
  El 𝟙 = ⊤
  El 𝔹 = Bool
  El (a₁ ⊜ a₂) = a₁ ≡ a₂ -- identity type trivial in this universe

  TYPE : Universe _ _
  TYPE = record { U = U; El = El }

  -- Example

  module Refl-all-the-way where

    x : El (true ⊜ true)
    x = refl

    -- y : El (true ⊜ false)
    -- ()

    z : El (_⊜_ {true ⊜ true} refl refl)
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
    swap : 𝔹 ⟷ 𝔹
    _◎⟷_ : {A B C : U} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)
    -- new combinators for _⊜_; for each type former (including the identity
    -- type), we have a combinator that expresses the structure of paths at that
    -- type. The exact list of combinators will be confirmed in the proof of
    -- univalence in the next universe
    ⊜-⊤l : tt ⊜ tt ⟷ 𝟙
    ⊜-⊤r : 𝟙 ⟷ tt ⊜ tt
    ⊜-𝔹₁l : true ⊜ true ⟷ 𝟙
    ⊜-𝔹₁r : 𝟙 ⟷ true ⊜ true
    ⊜-𝔹₂l : false ⊜ true ⟷ 𝟘
    ⊜-𝔹₂r : 𝟘 ⟷ false ⊜ true
    ⊜-𝔹₃l : true ⊜ false ⟷ 𝟘
    ⊜-𝔹₃r : 𝟘 ⟷ true ⊜ false
    ⊜-𝔹₄l : false ⊜ false ⟷ 𝟙
    ⊜-𝔹₄r : 𝟙 ⟷ false ⊜ false
    ⊜-⊜l : {A : U} {a a' : El A} → (p q : El (a ⊜ a')) → (p ⊜ q ⟷ 𝟙)
    ⊜-⊜r : {A : U} {a a' : El A} → (p q : El (a ⊜ a')) → (𝟙 ⟷ p ⊜ q)

  ! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
  ! swap = swap
  ! refl⟷ = refl⟷
  ! (c₁ ◎⟷ c₂) = ! c₂ ◎⟷ ! c₁
  ! ⊜-⊤l = ⊜-⊤r
  ! ⊜-⊤r = ⊜-⊤l
  ! ⊜-𝔹₁l = ⊜-𝔹₁r
  ! ⊜-𝔹₁r = ⊜-𝔹₁l
  ! ⊜-𝔹₂l = ⊜-𝔹₂r
  ! ⊜-𝔹₂r = ⊜-𝔹₂l
  ! ⊜-𝔹₃l = ⊜-𝔹₃r
  ! ⊜-𝔹₃r = ⊜-𝔹₃l
  ! ⊜-𝔹₄l = ⊜-𝔹₄r
  ! ⊜-𝔹₄r = ⊜-𝔹₄l
  ! (⊜-⊜l p q) = ⊜-⊜r p q
  ! (⊜-⊜r p q) = ⊜-⊜l p q

  eval : {A B : U} → (A ⟷ B) → El A → El B
  eval refl⟷ = id
  eval swap = not
  eval (c₁ ◎⟷ c₂) = (eval c₂) ○ (eval c₁)
  eval ⊜-⊤l refl = tt
  eval ⊜-⊤r tt = refl
  eval ⊜-𝔹₁l refl = tt
  eval ⊜-𝔹₁r tt = refl
  eval ⊜-𝔹₂l ()
  eval ⊜-𝔹₂r ()
  eval ⊜-𝔹₃l ()
  eval ⊜-𝔹₃r ()
  eval ⊜-𝔹₄l refl = tt
  eval ⊜-𝔹₄r tt = refl
  eval (⊜-⊜l _ _) refl = tt
  eval (⊜-⊜r p q) tt = proof-irrelevance p q

  data _⇔_ : {A B : U} → (A ⟷ B) → (A ⟷ B) → Set where
    refl⇔ : {A B : U} {c : A ⟷ B} → (c ⇔ c)
    _●_ : {A B : U} {c₁ c₂ c₃ : A ⟷ B} → (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
    idl◎l : {A B : U} {c : A ⟷ B} → (refl⟷ ◎⟷ c) ⇔ c
    idl◎r : {A B : U} {c : A ⟷ B} → c ⇔ (refl⟷ ◎⟷ c)
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
           𝟘; 𝟙; 𝔹;
           refl⟷; swap; _◎⟷_;
           refl⇔; idl◎l; idl◎r; _●_;
           ⊜-⊤l; ⊜-⊤r; ⊜-𝔹₁l; ⊜-𝔹₁r; ⊜-𝔹₂l; ⊜-𝔹₂r; ⊜-𝔹₃l; ⊜-𝔹₃r; ⊜-𝔹₄l; ⊜-𝔹₄r;
           ⊜-⊜l; ⊜-⊜r)
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

    x : El (_⊜_ {⇑ 𝔹} true true)
    x = refl

    y : El (_⊜_ {_⊜_ {⇑ 𝔹} true true} refl refl)
    y = refl

    z : El (_⊜_ {_⊜_ {_⊜_ {⇑ 𝔹} true true} refl refl} refl refl)
    z = refl

    -- identities between types; w₁ and w₂ are NOT equivalent but w₁, w₃, and w₄
    -- are all equivalent

    w₁ w₂ w₃ w₄ : El (_⊜_ {U0} 𝔹 𝔹)
    w₁ = refl⟷
    w₂ = swap
    w₃ = refl⟷ ◎⟷ refl⟷
    w₄ = swap ◎⟷ swap

    -- identities between combinators

    α₁₃ α₁₃' : El (_⊜_ {_⊜_ {U0} 𝔹 𝔹} w₁ w₃)
    α₁₃ = idl◎r
    α₁₃' = idl◎r ● refl⇔

    -- identities between 2-combinators

    X Y : El (_⊜_ {_⊜_ {_⊜_ {U0} 𝔹 𝔹} w₁ w₃} α₁₃ α₁₃')
    X eq = refl≈ eq
    Y eq = refl≈ eq

    -- last level of identities

    L : El (_⊜_ {_⊜_ {_⊜_ {_⊜_ {U0} 𝔹 𝔹} w₁ w₃} α₁₃ α₁₃'} X Y)
    L = refl

  -- Univalence

  module Univalence where

    -- High-level structure: for each pair of types A and B such that A ⊜ B, we
    -- define a function idtoeqv and show it is an equivalence

    tt≡tt≃⊤ : (tt ≡ tt) ≃ ⊤
    tt≡tt≃⊤ = (λ _ → tt) ,
              mkisequiv
                (λ _ → refl)
                (λ {tt → refl})
                (λ {refl → refl})

    b≡b≃⊤ : {b : Bool} → (b ≡ b) ≃ ⊤
    b≡b≃⊤ {b} = (λ _ → tt) ,
                mkisequiv
                  (λ _ → refl)
                  (λ {tt → refl})
                  (λ {r → proof-irrelevance refl r})

    p⊜q≃⊤ : {A : U₀} {a a' : El₀ A} → (p q : El₀ (a ⊜₀ a')) →
            El₀ (p ⊜₀ q) ≃ ⊤
    p⊜q≃⊤ refl q = (λ _ → tt) ,
                mkisequiv
                  (λ _ → proof-irrelevance refl q)
                  (λ {tt → refl})
                  (λ { p≡q → proof-irrelevance
                               (proof-irrelevance refl q)
                               p≡q})

    idtoeqv : {A B : U₀} → El (_⊜_ {U0} A B) → El₀ A ≃ El₀ B
    idtoeqv refl⟷ = refl≃
    idtoeqv swap = not , mkisequiv not
                           (λ { false → refl; true → refl})
                           (λ { false → refl; true → refl})
    idtoeqv (c₁ ◎⟷ c₂) = trans≃ (idtoeqv c₁) (idtoeqv c₂)
    idtoeqv ⊜-⊤l = tt≡tt≃⊤
    idtoeqv ⊜-⊤r = sym≃ tt≡tt≃⊤
    idtoeqv ⊜-𝔹₁l = b≡b≃⊤ {true}
    idtoeqv ⊜-𝔹₁r = sym≃ (b≡b≃⊤ {true})
    idtoeqv ⊜-𝔹₂l = (λ ()) , mkisequiv (λ ()) (λ ()) (λ ())
    idtoeqv ⊜-𝔹₂r = (λ ()) , mkisequiv (λ ()) (λ ()) (λ ())
    idtoeqv ⊜-𝔹₃l = (λ ()) , mkisequiv (λ ()) (λ ()) (λ ())
    idtoeqv ⊜-𝔹₃r = (λ ()) , mkisequiv (λ ()) (λ ()) (λ ())
    idtoeqv ⊜-𝔹₄l = b≡b≃⊤ {false}
    idtoeqv ⊜-𝔹₄r = sym≃ (b≡b≃⊤ {false})
    idtoeqv (⊜-⊜l p q) = p⊜q≃⊤ p q
    idtoeqv (⊜-⊜r p q) = sym≃ (p⊜q≃⊤ p q)

    univalence : (A B : U₀) → Set
    univalence A B =  isequiv (idtoeqv {A} {B})

    -- univalence is NOT a postulate; we can prove it! The proof is essentially
    -- the completeness of ⟷ with respect to equivalence

    true≡false→⊥ : (true ≡ false) → ⊥
    true≡false→⊥ ()

    false≡true→⊥ : (false ≡ true) → ⊥
    false≡true→⊥ ()

    ⊤≃Bool→⊥ : (⊤ ≃ Bool) → ⊥
    ⊤≃Bool→⊥ (f , mkisequiv g α β) =
      let ftt≡false = α false
          ftt≡true = α true
          true≡false = trans (sym ftt≡true) ftt≡false
      in true≡false→⊥ true≡false

    {-# NON_TERMINATING #-}
    univalenceP : (A B : U₀) → univalence A B
    univalenceP A B = mkisequiv comp {!!} {!!}
      where
        mutual
            comp : {A B : U₀} → (El₀ A ≃ El₀ B) → (A ⟷ B)
            comp {𝟘} {𝟘} _ = refl⟷
            comp {𝟘} {𝟙} (_ , mkisequiv g _ _) = ⊥-elim (g tt)
            comp {𝟘} {𝔹} (_ , mkisequiv g _ _) = ⊥-elim (g false)
            comp {𝟘} {_⊜₀_ {𝟘} () ()} (f , mkisequiv g α β)
            comp {𝟘} {_⊜₀_ {𝟙} tt tt} (f , mkisequiv g α β) = ⊥-elim (g refl)
            comp {𝟘} {_⊜₀_ {𝔹} false false} (f , mkisequiv g α β) = ⊥-elim (g refl)
            comp {𝟘} {_⊜₀_ {𝔹} true false} (f , mkisequiv g α β) = ⊜-𝔹₃r
            comp {𝟘} {_⊜₀_ {𝔹} false true} (f , mkisequiv g α β) = ⊜-𝔹₂r
            comp {𝟘} {_⊜₀_ {𝔹} true true} (f , mkisequiv g α β) = ⊥-elim (g refl)
            comp {𝟘} {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} (f , mkisequiv g α β) =
              let (f' , mkisequiv g' α' β') = (p⊜q≃⊤ a₃ a₄)
              in ⊥-elim (g (g' tt))
            comp {𝟙} {𝟘} (f , _) = ⊥-elim (f tt)
            comp {𝟙} {𝟙} _ = refl⟷
            comp {𝟙} {𝔹} eq = ⊥-elim (⊤≃Bool→⊥ eq)
            comp {𝟙} {_⊜₀_ {𝟘} () ()} (f , mkisequiv g α β)
            comp {𝟙} {_⊜₀_ {𝟙} tt tt} (f , mkisequiv g α β) = ⊜-⊤r
            comp {𝟙} {_⊜₀_ {𝔹} false false} (f , mkisequiv g α β) = ⊜-𝔹₄r
            comp {𝟙} {_⊜₀_ {𝔹} false true} (f , mkisequiv g α β) =
              ⊥-elim (false≡true→⊥ (f tt))
            comp {𝟙} {_⊜₀_ {𝔹} true false} (f , mkisequiv g α β) =
              ⊥-elim (true≡false→⊥ (f tt))
            comp {𝟙} {_⊜₀_ {𝔹} true true} (f , mkisequiv g α β) = ⊜-𝔹₁r
            comp {𝟙} {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} (f , mkisequiv g α β) = ⊜-⊜r a₃ a₄
            comp {𝔹} {𝟘} (f , _) = ⊥-elim (f false)
            comp {𝔹} {𝟙} eq = ⊥-elim (⊤≃Bool→⊥ (sym≃ eq))
            comp {𝔹} {𝔹} (f , mkisequiv g α β) = refl⟷
            comp {𝔹} {_⊜₀_ {𝟘} () ()}
            comp {𝔹} {_⊜₀_ {𝟙} tt tt} eq =
              ⊥-elim (⊤≃Bool→⊥ (trans≃ (sym≃ tt≡tt≃⊤) (sym≃ eq)))
            comp {𝔹} {_⊜₀_ {𝔹} false false} eq =
              ⊥-elim (⊤≃Bool→⊥ (trans≃ (sym≃ b≡b≃⊤) (sym≃ eq)))
            comp {𝔹} {_⊜₀_ {𝔹} false true} (f , mkisequiv g α β) =
              ⊥-elim (false≡true→⊥ (f true))
            comp {𝔹} {_⊜₀_ {𝔹} true false} (f , mkisequiv g α β) =
              ⊥-elim (true≡false→⊥ (f true))
            comp {𝔹} {_⊜₀_ {𝔹} true true} eq =
              ⊥-elim (⊤≃Bool→⊥ (trans≃ (sym≃ b≡b≃⊤) (sym≃ eq)))
            comp {𝔹} {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} eq =
              ⊥-elim (⊤≃Bool→⊥ (trans≃ (sym≃ (p⊜q≃⊤ a₃ a₄)) (sym≃ eq)))
            comp {_⊜₀_ {𝟘} a₁ a₂} {𝟘} (f , mkisequiv g α β) = ⊥-elim a₁
            comp {_⊜₀_ {𝟙} tt tt} {𝟘} (f , mkisequiv g α β) = ⊥-elim (f refl)
            comp {_⊜₀_ {𝔹} false false} {𝟘} (f , mkisequiv g α β) = ⊥-elim (f refl)
            comp {_⊜₀_ {𝔹} true false} {𝟘} (f , mkisequiv g α β) = ⊜-𝔹₃l
            comp {_⊜₀_ {𝔹} false true} {𝟘} (f , mkisequiv g α β) = ⊜-𝔹₂l
            comp {_⊜₀_ {𝔹} true true} {𝟘} (f , mkisequiv g α β) = ⊥-elim (f refl)
            comp {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} {𝟘} (f , mkisequiv g α β) =
              let (f' , mkisequiv g' α' β') = (p⊜q≃⊤ a₃ a₄)
              in ⊥-elim (f (g' tt))
            comp {_⊜₀_ {𝟘} a₁ a₂} {𝟙} (f , mkisequiv g α β) = ⊥-elim a₁
            comp {_⊜₀_ {𝟙} tt tt} {𝟙} (f , mkisequiv g α β) = ⊜-⊤l
            comp {_⊜₀_ {𝔹} false false} {𝟙} (f , mkisequiv g α β) = ⊜-𝔹₄l
            comp {_⊜₀_ {𝔹} false true} {𝟙} (f , mkisequiv g α β) =
              ⊥-elim (false≡true→⊥ (g tt))
            comp {_⊜₀_ {𝔹} true false} {𝟙} (f , mkisequiv g α β) =
              ⊥-elim (true≡false→⊥ (g tt))
            comp {_⊜₀_ {𝔹} true true} {𝟙} (f , mkisequiv g α β) = ⊜-𝔹₁l
            comp {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} {𝟙} (f , mkisequiv g α β) = ⊜-⊜l a₃ a₄
            comp {_⊜₀_ {𝟘} a₁ a₂} {𝔹} (f , mkisequiv g α β) = ⊥-elim a₁
            comp {_⊜₀_ {𝟙} tt tt} {𝔹} eq =
              ⊥-elim (⊤≃Bool→⊥ (trans≃ (sym≃ tt≡tt≃⊤) eq))
            comp {_⊜₀_ {𝔹} false false} {𝔹} eq =
              ⊥-elim (⊤≃Bool→⊥ (trans≃ (sym≃ b≡b≃⊤) eq))
            comp {_⊜₀_ {𝔹} false true} {𝔹} (f , mkisequiv g α β) =
              ⊥-elim (false≡true→⊥ (g true))
            comp {_⊜₀_ {𝔹} true false} {𝔹} (f , mkisequiv g α β) =
              ⊥-elim (true≡false→⊥ (g true))
            comp {_⊜₀_ {𝔹} true true} {𝔹} eq =
              ⊥-elim (⊤≃Bool→⊥ (trans≃ (sym≃ b≡b≃⊤) eq))
            comp {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} {𝔹} eq =
              ⊥-elim (⊤≃Bool→⊥ (trans≃ (sym≃ (p⊜q≃⊤ a₃ a₄)) eq))
            comp {_⊜₀_ {𝟘} a₁ a₂} {a₃ ⊜₀ a₄} (f , mkisequiv g α β) = ⊥-elim a₁
            comp {_⊜₀_ {𝟙} tt tt} {a₃ ⊜₀ a₄} (f , mkisequiv g α β) =
              ⊜-⊤l ◎⟷ (comp (𝟙≃a₁⊜a₂ f))
            comp {_⊜₀_ {𝔹} false false} {a₃ ⊜₀ a₄} (f , mkisequiv g α β) =
              ⊜-𝔹₄l ◎⟷ (comp (𝟙≃a₁⊜a₂ f))
            comp {_⊜₀_ {𝔹} false true} {_⊜₀_ {𝟘} a₃ a₄} (f , mkisequiv g α β) =
              ⊥-elim a₃
            comp {_⊜₀_ {𝔹} false true} {_⊜₀_ {𝟙} tt tt} (f , mkisequiv g α β) =
              ⊥-elim (false≡true→⊥ (g refl))
            comp {_⊜₀_ {𝔹} false true} {_⊜₀_ {𝔹} false false} (f , mkisequiv g α β) =
              ⊥-elim (false≡true→⊥ (g refl))
            comp {_⊜₀_ {𝔹} false true} {_⊜₀_ {𝔹} false true} (f , mkisequiv g α β) =
              refl⟷
            comp {_⊜₀_ {𝔹} false true} {_⊜₀_ {𝔹} true false} (f , mkisequiv g α β) =
              ⊜-𝔹₂l ◎⟷ ⊜-𝔹₃r
            comp {_⊜₀_ {𝔹} false true} {_⊜₀_ {𝔹} true true} (f , mkisequiv g α β) =
              ⊥-elim (false≡true→⊥ (g refl))
            comp {_⊜₀_ {𝔹} false true} {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} (f , mkisequiv g α β) =
              ⊜-𝔹₂l ◎⟷ (comp (⊥-elim ,
                (mkisequiv
                  (false≡true→⊥ ○ g)
                  (λ p → proof-irrelevance (⊥-elim (false≡true→⊥ (g p))) p)
                  (λ ⊥ → ⊥-elim ⊥))))
            comp {_⊜₀_ {𝔹} true false} {_⊜₀_ {𝟘} a₃ a₄} (f , mkisequiv g α β) =
              ⊥-elim a₃
            comp {_⊜₀_ {𝔹} true false} {_⊜₀_ {𝟙} tt tt} (f , mkisequiv g α β) =
              ⊜-𝔹₃l ◎⟷ ⊥-elim (true≡false→⊥ (g refl))
            comp {_⊜₀_ {𝔹} true false} {_⊜₀_ {𝔹} false false} (f , mkisequiv g α β) =
              ⊥-elim (true≡false→⊥ (g refl))
            comp {_⊜₀_ {𝔹} true false} {_⊜₀_ {𝔹} false true} (f , mkisequiv g α β) =
              ⊜-𝔹₃l ◎⟷ ⊜-𝔹₂r
            comp {_⊜₀_ {𝔹} true false} {_⊜₀_ {𝔹} true false} (f , mkisequiv g α β) =
              ⊜-𝔹₃l ◎⟷ ⊜-𝔹₃r
            comp {_⊜₀_ {𝔹} true false} {_⊜₀_ {𝔹} true true} (f , mkisequiv g α β) =
              ⊥-elim (true≡false→⊥ (g refl))
            comp {_⊜₀_ {𝔹} true false} {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} (f , mkisequiv g α β) =
              ⊜-𝔹₃l ◎⟷ (comp (⊥-elim ,
                (mkisequiv
                  (true≡false→⊥ ○ g)
                  (λ p → proof-irrelevance (⊥-elim (true≡false→⊥ (g p))) p)
                  (λ ⊥ → ⊥-elim ⊥))))
            comp {_⊜₀_ {𝔹} true true} {a₃ ⊜₀ a₄} (f , mkisequiv g α β) =
              ⊜-𝔹₁l ◎⟷ (comp (𝟙≃a₁⊜a₂ f))
            comp {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} {_⊜₀_ {𝟘} () a₆} eq
            comp {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} {_⊜₀_ {𝟙} tt tt} eq =
              (comp (p⊜q≃⊤ a₃ a₄)) ◎⟷ ⊜-⊤r
            comp {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} {_⊜₀_ {𝔹} false false} eq =
              (comp (p⊜q≃⊤ a₃ a₄)) ◎⟷ ⊜-𝔹₄r
            comp {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} {_⊜₀_ {𝔹} false true} eq =
              (comp (p⊜q≃⊤ a₃ a₄)) ◎⟷ comp (trans≃ (sym≃ (p⊜q≃⊤ a₃ a₄)) eq)
            comp {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} {_⊜₀_ {𝔹} true false} eq =
              (comp (p⊜q≃⊤ a₃ a₄)) ◎⟷ comp (trans≃ (sym≃ (p⊜q≃⊤ a₃ a₄)) eq)
            comp {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} {_⊜₀_ {𝔹} true true} eq =
              (comp (p⊜q≃⊤ a₃ a₄)) ◎⟷ ⊜-𝔹₁r
            comp {_⊜₀_ {a₁ ⊜₀ a₂} a₃ a₄} {_⊜₀_ {a₅ ⊜₀ a₆} a₇ a₈} eq =
              (comp (p⊜q≃⊤ a₃ a₄)) ◎⟷ (comp (sym≃ (p⊜q≃⊤ a₇ a₈)))

            𝟙≃a₁⊜a₂ : {A B : U₀} {a : El₀ A} {a₃ a₄ : El₀ B} →
                      (a ≡ a → a₃ ≡ a₄) → El₀ 𝟙 ≃ El₀ (a₃ ⊜₀ a₄)
            𝟙≃a₁⊜a₂ f = ((λ _ → f refl) ,
                         mkisequiv
                           (λ _ → tt)
                           (λ p → proof-irrelevance (f refl) p)
                           (λ tt → refl))

------------------------------------------------------------------------------
