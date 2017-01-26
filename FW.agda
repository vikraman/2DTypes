{-# OPTIONS --without-K #-}

module FW where

import Level as L using (_⊔_)
open import Data.Nat using (ℕ; suc)
open import Data.Empty using (⊥)
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Vec
open import Function renaming (_∘_ to _○_)

infixr 8  _∘_   -- path composition
infix  4  _≡_   -- propositional equality
infix  4  _∼_   -- homotopy between two functions (the same as ≡ by univalence)
infix  4  _≃_   -- type of equivalences
infix  2  _∎      -- equational reasoning
infixr 2  _≡⟨_⟩_  -- equational reasoning

------------------------------------------------------------------------------
-- Identity types

-- Our own version of refl that makes 'a' explicit

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)

-- Induction principle for identity types

pathInd : ∀ {u ℓ} → {A : Set u} →
          (C : {x y : A} → x ≡ y → Set ℓ) →
          (c : (x : A) → C (refl x)) →
          ({x y : A} (p : x ≡ y) → C p)
pathInd C c (refl x) = c x

------------------------------------------------------------------------------
-- Types are higher groupoids. We have paths between the elements
-- (refl, sym, trans) then we have path between paths, e.g., paths
-- between p and (trans p refl) and paths between (sym (sym p)) and p
-- etc.

-- Lemma 2.1.1

! : ∀ {u} → {A : Set u} {x y : A} → (x ≡ y) → (y ≡ x)
! = pathInd (λ {x} {y} _ → y ≡ x) refl

-- Lemma 2.1.2

_∘_ : ∀ {u} → {A : Set u} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_∘_ {u} {A} {x} {y} {z} p q =
  pathInd {u}
    (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (x ≡ z)))
    (λ x z q → pathInd (λ {x} {z} _ → x ≡ z) refl {x} {z} q)
    {x} {y} p z q

-- Lemma 2.1.4

-- p = p . refl

unitTransR : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ p ∘ refl y)
unitTransR {A} {x} {y} p =
  pathInd
    (λ {x} {y} p → p ≡ p ∘ (refl y))
    (λ x → refl (refl x))
    {x} {y} p

-- p = refl . p

unitTransL : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ refl x ∘ p)
unitTransL {A} {x} {y} p =
  pathInd
    (λ {x} {y} p → p ≡ (refl x) ∘ p)
    (λ x → refl (refl x))
    {x} {y} p

-- ! p . p = refl

invTransL : {A : Set} {x y : A} → (p : x ≡ y) → (! p ∘ p ≡ refl y)
invTransL {A} {x} {y} p =
  pathInd
    (λ {x} {y} p → ! p ∘ p ≡ refl y)
    (λ x → refl (refl x))
    {x} {y} p

-- p . ! p = refl

invTransR : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → (p ∘ ! p ≡ refl x)
invTransR {ℓ} {A} {x} {y} p =
  pathInd
    (λ {x} {y} p → p ∘ ! p ≡ refl x)
    (λ x → refl (refl x))
    {x} {y} p

-- ! (! p) = p

invId : {A : Set} {x y : A} → (p : x ≡ y) → (! (! p) ≡ p)
invId {A} {x} {y} p =
  pathInd
    (λ {x} {y} p → ! (! p) ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

-- p . (q . r) = (p . q) . r

assocP : {A : Set} {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) →
         (p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
assocP {A} {x} {y} {z} {w} p q r =
  pathInd
    (λ {x} {y} p → (z : A) → (w : A) → (q : y ≡ z) → (r : z ≡ w) →
      p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
    (λ x z w q r →
      pathInd
        (λ {x} {z} q → (w : A) → (r : z ≡ w) →
          (refl x) ∘ (q ∘ r) ≡ ((refl x) ∘ q) ∘ r)
        (λ x w r →
          pathInd
            (λ {x} {w} r →
              (refl x) ∘ ((refl x) ∘ r) ≡
              ((refl x) ∘ (refl x)) ∘ r)
            (λ x → (refl (refl x)))
            {x} {w} r)
        {x} {z} q w r)
    {x} {y} p z w q r

-- ! (p ∘ q) ≡ ! q ∘ ! p

invComp : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) →
          ! (p ∘ q) ≡ ! q ∘ ! p
invComp {A} {x} {y} {z} p q =
  pathInd
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → ! (p ∘ q) ≡ ! q ∘ ! p)
    (λ x z q →
      pathInd
        (λ {x} {z} q → ! (refl x ∘ q) ≡ ! q ∘ ! (refl x))
        (λ x → refl (refl x))
        {x} {z} q)
    {x} {y} p z q

-- Introduce equational reasoning syntax to simplify proofs

_≡⟨_⟩_ : ∀ {u} → {A : Set u} (x : A) {y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_ ≡⟨ p ⟩ q = p ∘ q

bydef : ∀ {u} → {A : Set u} {x : A} → (x ≡ x)
bydef {u} {A} {x} = refl x

_∎ : ∀ {u} → {A : Set u} (x : A) → x ≡ x
_∎ x = refl x

------------------------------------------------------------------------------
-- Functions are functors

-- Lemma 2.2.1
-- computation rule: ap f (refl x) = refl (f x)

ap : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A} →
     (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {ℓ} {ℓ'} {A} {B} {x} {y} f p =
  pathInd -- on p
    (λ {x} {y} p → f x ≡ f y)
    (λ x → refl (f x))
    {x} {y} p

-- Lemma 2.2.2

apfTrans : ∀ {u} → {A B : Set u} {x y z : A} →
  (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q)
apfTrans {u} {A} {B} {x} {y} {z} f p q =
  pathInd {u}
    (λ {x} {y} p → (z : A) → (q : y ≡ z) →
      ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q))
    (λ x z q →
      pathInd {u}
        (λ {x} {z} q →
          ap f (refl x ∘ q) ≡ (ap f (refl x)) ∘ (ap f q))
        (λ x → refl (refl (f x)))
        {x} {z} q)
    {x} {y} p z q

apfInv : ∀ {u} → {A B : Set u} {x y : A} → (f : A → B) → (p : x ≡ y) →
         ap f (! p) ≡ ! (ap f p)
apfInv {u} {A} {B} {x} {y} f p =
  pathInd {u}
    (λ {x} {y} p → ap f (! p) ≡ ! (ap f p))
    (λ x → refl (ap f (refl x)))
    {x} {y} p

apfComp : {A B C : Set} {x y : A} → (f : A → B) → (g : B → C) → (p : x ≡ y) →
          ap g (ap f p) ≡ ap (g ○ f) p
apfComp {A} {B} {C} {x} {y} f g p =
  pathInd
    (λ {x} {y} p → ap g (ap f p) ≡ ap (g ○ f) p)
    (λ x → refl (ap g (ap f (refl x))))
    {x} {y} p

apfId : {A : Set} {x y : A} → (p : x ≡ y) → ap id p ≡ p
apfId {A} {x} {y} p =
  pathInd
    (λ {x} {y} p → ap id p ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

-- Transport; Lifting

-- Lemma 2.3.1

transport : ∀ {ℓ ℓ'} → {A : Set ℓ} {x y : A} →
  (P : A → Set ℓ') → (p : x ≡ y) → P x → P y
transport {ℓ} {ℓ'} {A} {x} {y} P p =
  pathInd -- on p
    (λ {x} {y} p → (P x → P y))
    (λ _ → id)
    {x} {y} p

stransport : ∀ {ℓ} → {A : Set ℓ} {x y : A} → (p : x ≡ y) → A → A
stransport {ℓ} {A} {x} {y} p = transport {ℓ} {ℓ} {A} {x} {y} (λ _ → A) p

-- Lemma 2.3.2

liftP : {A : Set} {x y : A} {P : A → Set} → (u : P x) → (p : x ≡ y) →
        (x , u) ≡ (y , transport P p u)
liftP {A} {x} {y} {P} u p =
  pathInd
    (λ {x} {y} p → ((u : P x) → (x , u) ≡ (y , transport P p u)))
    (λ x u → refl (x , u))
    {x} {y} p u

-- Lemma 2.3.4 (dependent version of Lemma 2.2.1)

apd : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : A → Set ℓ'} {x y : A} → (f : (a : A) → B a) →
  (p : x ≡ y) → (transport B p (f x) ≡ f y)
apd {ℓ} {ℓ'} {A} {B} {x} {y} f p =
  pathInd
    (λ {x} {y} p → transport B p (f x) ≡ f y)
    (λ x → refl (f x))
    {x} {y} p

-- Lemma 2.3.5

transportconst : {A : Set} {x y : A} → (B : Set) → (p : x ≡ y) → (b : B) →
                 (transport (λ _ → B) p b ≡ b)
transportconst {A} {x} {y} B p b =
  pathInd
    (λ {x} {y} p → transport (λ _ → B) p b ≡ b)
    (λ _ → refl b)
    {x} {y} p

-- Eqs. 2.3.6 and 2.3.7

transportconst-ap : {A : Set} {x y : A} → (B : Set) → (p : x ≡ y) →
  (f : A → B) → (f x ≡ f y) → (transport (λ _ → B) p (f x) ≡ f y)
transportconst-ap {A} {x} {y} B p f α =
  transportconst B p (f x) ∘ α

ap-transportconst : {A : Set} {x y : A} → (B : Set) → (p : x ≡ y) →
  (f : A → B) → (transport (λ _ → B) p (f x) ≡ f y) → (f x ≡ f y)
ap-transportconst {A} {x} {y} B p f α =
  (! (transportconst B p (f x))) ∘ α

-- Lemma 2.3.8

apd-transportconst : {A : Set} {x y : A} → (B : Set) → (p : x ≡ y) →
  (f : A → B) → (apd f p ≡ transportconst B p (f x) ∘ ap f p)
apd-transportconst {A} {x} {y} B p f =
  pathInd -- on p
    (λ {x} {y} p → apd f p ≡ transportconst B p (f x) ∘ ap f p)
    (λ x → refl (refl (f x)))
    {x} {y} p

-- Lemma 2.3.9

transport-comp : {A : Set} {x y z : A} → (P : A → Set) →
  (p : x ≡ y) → (q : y ≡ z) →
  (u : P x) → transport P q (transport P p u) ≡ transport P (p ∘ q) u
transport-comp {A} {x} {y} {z} P p q u =
  pathInd -- on p
    (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (u : P x) →
      transport P q (transport P p u) ≡ transport P (p ∘ q) u))
    (λ x z q u →
      pathInd -- on q
        (λ {x} {z} q → ((u : P x) →
          transport P q (transport P (refl x) u) ≡
          transport P (refl x ∘ q) u))
        (λ x u → refl u)
        {x} {z} q u)
    {x} {y} p z q u

-- Lemma 2.3.10

transport-f : ∀ {ℓ ℓ' ℓ''} → {A : Set ℓ} {B : Set ℓ'} {x y : A} →
  (f : A → B) → (P : B → Set ℓ'') →
  (p : x ≡ y) → (u : P (f x)) →
  transport (P ○ f) p u ≡ transport P (ap f p) u
transport-f {ℓ} {ℓ'} {ℓ''} {A} {B} {x} {y} f P p u =
  pathInd -- on p
    (λ {x} {y} p → (u : P (f x)) →
      transport (P ○ f) p u ≡ transport P (ap f p) u)
    (λ x u → refl u)
    {x} {y} p u

-- Lemma 2.3.11

transport-fam : ∀ {ℓ} → {A : Set ℓ} {x y : A} → (P Q : A → Set ℓ) →
  (f : (a : A) → P a → Q a) → (p : x ≡ y) → (u : P x) →
  transport Q p (f x u) ≡ f y (transport P p u)
transport-fam {ℓ} {A} {x} {y} P Q f p u =
  pathInd {ℓ} -- on p
    (λ {x} {y} p → (u : P x) →
      transport Q p (f x u) ≡ f y (transport P p u))
    (λ x u → refl (f x u))
    {x} {y} p u

-------------------------------------------------------------------------------
-- Homotopies and equivalences

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} →
      (f g : (x : A) → P x) → Set (L._⊔_ ℓ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

-- Lemma 2.4.2

refl∼ : {A B : Set} {f : A → B} → (f ∼ f)
refl∼ {A} {B} {f} x = refl (f x)

sym∼ : {A B : Set} {f g : A → B} → (f ∼ g) → (g ∼ f)
sym∼ H x = ! (H x)

trans∼ : {A B : Set} {f g h : A → B} → (f ∼ g) → (g ∼ h) → (f ∼ h)
trans∼ H G x = H x ∘ G x

-- Quasi-inverses

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) :
  Set (L._⊔_ ℓ ℓ') where
  constructor mkqinv
  field
    g : B → A
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

-- Example 2.4.7

idqinv : ∀ {ℓ} → {A : Set ℓ} → qinv {ℓ} {ℓ} {A} {A} id
idqinv = record {
           g = id ;
           α = λ b → refl b ;
           β = λ a → refl a
         }

-- Equivalences

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) :
  Set (L._⊔_ ℓ ℓ') where
  constructor mkisequiv
  field
    g : B → A
    α : (f ○ g) ∼ id
    h : B → A
    β : (h ○ f) ∼ id

equiv₁ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {f : A → B} → qinv f → isequiv f
equiv₁ (mkqinv qg qα qβ) = mkisequiv qg qα qg qβ

equiv₂ : {A B : Set} {f : A → B} → isequiv f → qinv f
equiv₂ {A} {B} {f} (mkisequiv ig iα ih iβ) =
  record {
    g = ig ;
    α = iα ;
    β = λ x → (! (iβ (ig (f x)))) ∘ (ap ih (iα (f x))) ∘ (iβ x)
    }

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (L._⊔_ ℓ ℓ')
A ≃ B = Σ (A → B) isequiv

-- Lemma 2.4.12

idequiv : ∀ {ℓ} {A : Set ℓ} → A ≃ A
idequiv = (id , equiv₁ idqinv)

symequiv : {A B : Set} → A ≃ B → B ≃ A
symequiv (f , feq) with equiv₂ feq
... | mkqinv g α β = (g , equiv₁ (mkqinv f β α))

------------------------------------------------------------------------------
-- Now we try to understand the structure of the paths. For how are
-- paths defined on pairs related to the paths on the individual
-- elements...

-- Sec. 2.6: cartesian products
-- implicit use of recP below to that arguments of product types are
-- pairs; "eliminators" for paths on pairs

ap_pr₁ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
        (x ≡ y) → (proj₁ x ≡ proj₁ y)
ap_pr₁ = ap proj₁

ap_pr₂ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
         (x ≡ y) → (proj₂ x ≡ proj₂ y)
ap_pr₂ = ap proj₂

-- Eq. 2.6.1

fpair : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
        (x ≡ y) → ((proj₁ x ≡ proj₁ y) × (proj₂ x ≡ proj₂ y))
fpair p = (ap_pr₁ p , ap_pr₂ p)

-- "constructor" for paths on pairs

pair⁼ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
        (proj₁ x ≡ proj₁ y) × (proj₂ x ≡ proj₂ y) → (x ≡ y)
pair⁼ {ℓ} {ℓ'} {A} {B} {(a , b)} {(a' , b')} (p , q) =
  pathInd -- on p
    (λ {a} {a'} p → ((b : B) → (b' : B) → (q : b ≡ b') →
      ((a , b) ≡ (a' , b'))))
    (λ a b b' q →
      pathInd -- on q
        (λ {b} {b'} q → (a , b) ≡ (a , b'))
        (λ b → refl (a , b))
        {b} {b'} q)
    {a} {a'} p b b' q

-- propositional uniqueness for pairs as a consequence

upair : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {z : A × B} → z ≡ (proj₁ z , proj₂ z)
upair {ℓ} {ℓ'} {A} {B} {z} =
  pair⁼ {ℓ} {ℓ'} {A} {B} {z} {(proj₁ z , proj₂ z)}
    (refl (proj₁ z) , refl (proj₂ z))

-- "computation rules" for paths on pairs

βpair : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
        (r : x ≡ y) → (pair⁼ (fpair r) ≡ r)
βpair {ℓ} {ℓ'} {A} {B} {x} {y} r =
  pathInd -- on r
    (λ {x} {y} r → pair⁼ (fpair r) ≡ r)
    (λ x → refl (refl (proj₁ x , proj₂ x)))
    {x} {y} r

-- propositional uniqueness principle for pairs of paths

upairp : ∀ {u} {A B : Set u} {x y : A × B} {r : x ≡ y} →
         r ≡ pair⁼ (ap_pr₁ r , ap_pr₂ r)
upairp {u} {A} {B} {x} {y} {r} = ! (βpair {u} {u} {A} {B} {x} {y} r)

-- Theorem 2.6.4

_×d_ : {Z : Set} → (A B : Z → Set) → (z : Z) → Set
_×d_ {Z} A B z = A z × B z

-- Theorem 2.6.5

pairf : {A B A' B' : Set} {g : A → A'} {h : B → B'} →
        A × B → A' × B'
pairf {A} {B} {A'} {B'} {g} {h} x = (g (proj₁ x) , h (proj₂ x))

------------------------------------------------------------------------------
-- Sec. 2.7: Σ-types

sigma⁼ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {w w' : Σ A P} →
         (Σ (proj₁ w ≡ proj₁ w') (λ p → transport P p (proj₂ w) ≡ proj₂ w'))
         → (w ≡ w')
sigma⁼ {ℓ} {ℓ'} {A} {P} {(w₁ , w₂)} {(w₁' , w₂')} (p , q) =
  pathInd -- on p
    (λ {w₁} {w₁'} p → (w₂ : P w₁) → (w₂' : P w₁') →
                     (q : transport P p w₂ ≡ w₂') → ((w₁ , w₂) ≡ (w₁' , w₂')))
    (λ w₁ w₂ w₂' q →
      pathInd -- on q
        (λ {w₂} {w₂'} q → (w₁ , w₂) ≡ (w₁ , w₂'))
        (λ w₂ → refl (w₁ , w₂))
        {w₂} {w₂'} q)
    {w₁} {w₁'} p w₂ w₂' q

-- Thm 2.7.4 transport

transportΣ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {P : A → Set ℓ'} {Q : Σ A P → Set ℓ''}
  {x y : A} → (p : x ≡ y) → (uz : Σ (P x) (λ u → Q (x , u))) →
  transport (λ x → Σ (P x) (λ u → Q (x , u))) p uz ≡
    (transport P p (proj₁ uz) ,
     transport Q (sigma⁼ (p , refl (transport P p (proj₁ uz)))) (proj₂ uz))
transportΣ {ℓ} {ℓ'} {ℓ''} {A} {P} {Q} {x} {y} p (u , z) =
  pathInd -- on p
    (λ {x} {y} p → (uz : Σ (P x) (λ u → Q (x , u))) →
      transport (λ x → Σ (P x) (λ u → Q (x , u))) p uz ≡
      (transport P p (proj₁ uz) ,
        transport Q (sigma⁼ (p , refl (transport P p (proj₁ uz)))) (proj₂ uz)))
    (λ x uz → refl uz)
    {x} {y} p (u , z)

------------------------------------------------------------------------------
-- Sec. 2.8: Unit type

unitPath : {x y : ⊤} → (x ≡ y) ≃ ⊤
unitPath {x} {y} =
  ((λ _ → tt) , equiv₁ (record {
    g = λ _ → refl tt ;
    α = λ _ → refl tt ;
    β = λ p → pathInd
                (λ {_} {_} p → refl tt ≡ p)
                (λ _ → refl (refl tt))
                {x} {y} p
  }))

------------------------------------------------------------------------------
-- Sec. 2.9: Pi types; function extensionality

happly : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (a : A) → B a} →
         (f ≡ g) → (f ∼ g)
happly {ℓ} {ℓ'} {A} {B} {f} {g} p =
  pathInd
    (λ {f} {g} p → f ∼ g)
    (λ f x → refl (f x))
    {f} {g} p

postulate
  funextP : {A : Set} {B : A → Set} {f g : (a : A) → B a} →
            isequiv {A = f ≡ g} {B = f ∼ g} happly

funext : {A : Set} {B : A → Set} {f g : (a : A) → B a} →
         (f ∼ g) → (f ≡ g)
funext = isequiv.g funextP

------------------------------------------------------------------------------
-- Sec. 2.10: Universes; univalence

idtoeqv : {A B : Set} → (A ≡ B) → (A ≃ B)
idtoeqv {A} {B} p =
  pathInd
    (λ {A} {B} p → A ≃ B)
    (λ A → idequiv)
    {A} {B} p

postulate
  univalence : {A B : Set} → (A ≡ B) ≃ (A ≃ B)

------------------------------------------------------------------------------
-- Bool

noteq : Bool ≃ Bool
noteq = not , equiv₁ (mkqinv not
                       (λ { false → refl false; true → refl true})
                       (λ { false → refl false; true → refl true}))

notpath : Bool ≡ Bool
notpath = isequiv.g (proj₂ univalence) noteq

-- Now go back and look at what happens to notpath when

------------------------------------------------------------------------------






















{--
------------------------------------------------------------------------------
-- Courtesy of Wolfram Kahl, a dependent cong₂

cong₂D! : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
         (f : (x : A) → B x → C)
       → {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
       → (x₂≡x₁ : x₂ ≡ x₁) → subst B x₂≡x₁ y₂ ≡ y₁ → f x₁ y₁ ≡ f x₂ y₂
cong₂D! f refl refl = refl

------------------------------------------------------------------------------
-- U0

-- Have:
-- Objects: 𝟚, false, true
-- Functions: id, not,
-- Identity Types: false≡false, false≡true, true≡false, true≡true
-- Paths: refl-false, refl-true

data `U0 : Set where
  `𝟚    : `U0
  `fun  : `U0
  `f≡f  : `U0
  `f≡t  : `U0
  `t≡f  : `U0
  `t≡t  : `U0

El0 : `U0 → Set
El0 `𝟚 = Bool
El0 `fun = Bool → Bool
El0 `f≡f = false ≡ false
El0 `f≡t = false ≡ true
El0 `t≡f = true ≡ false
El0 `t≡t = true ≡ true

𝟚 : Set
𝟚 = Bool

-- only C's we allow are the ones returning a set in `U0
J0 : (C : (b₁ b₂ : 𝟚) → (b₁ ≡ b₂) → `U0) →
     ((b : 𝟚) → El0 (C b b refl)) →
     (b₁ b₂ : 𝟚) → (p : b₁ ≡ b₂) → El0 (C b₁ b₂ p)
J0 C c b .b refl = c b

! : (b₁ b₂ : 𝟚) → (p : b₁ ≡ b₂) → (b₂ ≡ b₁)
! = J0 (λ {false false _ → {!!};
           false true _ → {!!};
           true false _ → {!!};
           true true _ → ?})
       (λ b → {!!})

(λ { false false p → `f≡f;
            false true p → `t≡f;
            true false p → `f≡t;
            true true p → `t≡t})
       ? -- (λ {false → refl; true → refl})



data `U : Set
data 𝟚⟷𝟚 : Set

data `U where
  `𝟚 : `U
  1-Paths : `U -- 𝟚 ⟷ 𝟚
  2-Paths : (c₁ c₂ : 𝟚⟷𝟚) → `U

data 𝟚⟷𝟚 where
  `id : 𝟚⟷𝟚
  `not : 𝟚⟷𝟚

data _⇔_ : (c₁ c₂ : 𝟚⟷𝟚) → Set where
  `id2 : {c : 𝟚⟷𝟚} → c ⇔ c


El : `U → Set
El `𝟚 = 𝟚
El 1-Paths = 𝟚⟷𝟚
El (2-Paths c₁ c₂) = c₁ ⇔ c₂

-- induction principle (J generalized)

1pathInd : ∀ {ℓ} → (C : (𝟚⟷𝟚) → Set ℓ) →
          (cid : C `id) → (cnot : C `not) →
          (p : 𝟚⟷𝟚) → C p
1pathInd C cid cnot `id = cid
1pathInd C cid cnot `not = cnot

J𝟚 : (cid : 𝟚⟷𝟚) → (cnot : 𝟚⟷𝟚) →
     (p : 𝟚⟷𝟚) → 𝟚⟷𝟚
J𝟚 cid cnot `id = cid
J𝟚 cid cnot `not = cnot

-- Lemma 2.1.1

_⁻¹ : 𝟚⟷𝟚 → 𝟚⟷𝟚
_⁻¹ = 1pathInd (λ _ → 𝟚⟷𝟚) `id `not

-- Will use pattern-matching instead of the explicit induction principle in the
-- following

! : 𝟚⟷𝟚 → 𝟚⟷𝟚
! `id = `id
! `not = `not

-- Lemma 2.1.2
_∘_ : 𝟚⟷𝟚 → 𝟚⟷𝟚 → 𝟚⟷𝟚
`id ∘ `id = `id
`id ∘ `not = `not
`not ∘ `id = `not
`not ∘ `not = `id

-- Lemma 2.1.4

-- p = p . refl

unitTransR : (p : 𝟚⟷𝟚) → p ⇔ (p ∘ `id)
unitTransR `id = `id2
unitTransR `not = `id2

-- p = refl . p

unitTransL : (p : 𝟚⟷𝟚) → p ⇔ (`id ∘ p)
unitTransL `id = `id2
unitTransL `not = `id2

-- ! p . p = refl

invTransL : (p : 𝟚⟷𝟚) → (! p ∘ p) ⇔ `id
invTransL `id = `id2
invTransL `not = `id2

-- p . ! p = refl

invTransR : (p : 𝟚⟷𝟚) → (p ∘ ! p) ⇔ `id
invTransR `id = `id2
invTransR `not = `id2

-- ! (! p) = p

invId : (p : 𝟚⟷𝟚) → ! (! p) ⇔ p
invId `id = `id2
invId `not = `id2

-- p . (q . r) = (p . q) . r

assocP : (p q r : 𝟚⟷𝟚) → (p ∘ (q ∘ r)) ⇔ ((p ∘ q) ∘ r)
assocP `id `id `id = `id2
assocP `id `id `not = `id2
assocP `id `not `id = `id2
assocP `id `not `not = `id2
assocP `not `id `id = `id2
assocP `not `id `not = `id2
assocP `not `not `id = `id2
assocP `not `not `not = `id2

-- ! (p ∘ q) ≡ ! q ∘ ! p

invComp : (p q : 𝟚⟷𝟚) → (! (p ∘ q)) ⇔ (! q ∘ ! p)
invComp `id `id = `id2
invComp `id `not = `id2
invComp `not `id = `id2
invComp `not `not = `id2

-- Looks like ap, apd, transport are all vacuous in our case...

------------------------------------------------------------------------------
-- Univalence

-- Interpretation

_∼_ : {A B : Set} → (f g : A → B) → Set
_∼_ {A} f g = (a : A) → f a ≡ g a

record isequiv {A B : Set} (f : A → B) : Set where
  constructor mkisequiv
  field
    g : B → A
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

_≅_ : Set → Set → Set
A ≅ B = Σ[ f ∈ (A → B) ] isequiv f

pathtoequiv : 𝟚⟷𝟚 → 𝟚 ≅ 𝟚
pathtoequiv `id =
  id , mkisequiv id (λ _ → refl) (λ _ → refl)
pathtoequiv `not =
  not , mkisequiv not
          (λ { false → refl ; true → refl })
          (λ { false → refl ; true → refl })

equivtopath : 𝟚 ≅ 𝟚 → 𝟚⟷𝟚
equivtopath (f , mkisequiv g α β) =
  case f true of (λ { false → `not ; true → `id })

postulate
  funext : {f g : Bool → Bool} → (f ∼ g) → (f ≡ g)

univalence : (𝟚⟷𝟚) ≅ (𝟚 ≅ 𝟚)
univalence = pathtoequiv , mkisequiv equivtopath α β
  where β :  (equivtopath ○ pathtoequiv) ∼ id
        β `id = refl
        β `not = refl

        α : (pathtoequiv ○ equivtopath) ∼ id
        α (f , mkisequiv g h₁ h₂) with equivtopath (f , mkisequiv g h₁ h₂)
        ... | `id = cong₂D! _,_ (funext {!!}) {!!}
        ... | `not = cong₂D! _,_ (funext {!!}) {!!}

------------------------------------------------------------------------------
-- Lemma 2.2.1
-- computation rule: ap f (refl x) = refl (f x)

-- vacuous in our case: there is only function in U → U; it maps Bool to itself

-- Lemma 2.2.2

apfTrans : {A B C : U} →
  (f : U → U) → (p : A ⟷ B) → (q : B ⟷ C) →
  Paths (ap f (p ∘ q)) ⟷ Paths ((ap f p) ∘ (ap f q))
apfTrans f `id `id = `id
apfTrans f `id `not = unitTransL (ap f `not)
apfTrans f `not `id = unitTransR (ap f `not)
apfTrans f `not `not with f `𝟚
... | `𝟚 = ! (invTransL `not)
... | Paths `id = `id
... | Paths `not = `id

-- transport

--transport : {A B : U} → (P : U → U) → (p : A ⟷ B) → El (P A) → El (P B)
--transport P `id = id
--transport P `not with P `𝟚
--... | `𝟚 = not
--... | Paths `id = id
--... | Paths `not = id

-- Dependent ap

--apd : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : A → Set ℓ'} {x y : A} → (f : (a : A) → B a) →
--  (p : x ≡ y) → (transport B p (f x) ≡ f y)
--apd : {A B : U} {P : U → U} → (f : (u : U) → El (P u)) →
--  (p : x ⟷ y) → (Paths (transport P p (f x)) ⟷ Paths (f y))
--apd = {!!}

-- Level 2 induction principle

2pathInd : ∀ {ℓ} {c₁ c₂ : 𝟚⟷𝟚} → (C : c₁ ⇔ c₂ → Set ℓ) →
          (cid2 : C `id2) → (cnotinv : C `notinv) →
          (p : [𝟚⟷𝟚]⇔[𝟚⟷𝟚]) → C p
2pathInd C cid2 cnotinv `id2 = cid2
2pathInd C cid2 cnotinv `notinv = cnotinv

------------------------------------------------------------------------------
--}
