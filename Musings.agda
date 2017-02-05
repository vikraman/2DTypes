{-# OPTIONS --without-K #-}

-- Note: everything in this file is 'semantic', in the sense that
-- Pi makes no appearance at all.  Of course, thinking about Pi is
-- what underlies all of this.

-- The basic thought provess is: what if we were to try to implement
-- a system where univalence is true?  This is difficult because
-- univalence is *false* in the 'bit model' of a computer.  It is
-- neither true nor false in Agda itself; that is certainly better, but
-- still not quite enough.

-- Fundamental idea: use a 2-level system.  There is an 'implementation
-- layer' where things are not assumed univalent.  The leading example
-- in all the code below is A × B versus B × A.  In Agda's Set₀, these
-- are not ≡.  They are also not not ≡.  That helps!

-- So we first figure out how to manipulate A × B and B × A in ways
-- such that they become easily exchangeable.

-- Part of the idea is that A × B ≃ B × A induces a *non-trivial*
-- automorphism of (A × B ⊎ B × A).  It is important to move from
-- equivalences to automorphisms (see Dan Christensen's slides for
-- more on this topic).

-- The second idea is that this automorphism allows one to
-- "make a choice", and represent (A × B ⊎ B × A) using
-- A × B × Bool instead.  (B × A × Bool works too!)
-- The details are worked out below.  This then lifts to
-- being able to show (see the-same) that functions from
-- A × B → C and B × A → C are "the same" under that
-- interpretation.  With a bit more work, that can be lifted
-- to the dependent setting, i.e. C a b.  See 'the-sameD'.

-- The third idea, to build the layer where univalence works,
-- is to make use of fractional types.  Basically, move from
-- A × B × Bool to A × B × (Bool / #swap).  [Here Bool has been
-- identified with (#id ⊎ #swap)].  The latter should be
-- A × B × 1 ≃ A × B.

-- Note that the move from the implementation layer to the outer
-- layer is NOT INFORMATION PRESERVING.  It forgets 1 bit.
module Musings where

open import Level using (Level)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; _,_; Σ)
open import Data.Bool using (Bool; true; false)
open import Function using (id;_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong₂; cong; subst; inspect; [_])

open import Equiv
open import TypeEquiv

-- A few 'obvious' equivalences relating to how we might
-- actually implement A × B in such a way that the underlying
-- representation is hidden (and irrelevant).
-- [A lot of this is known, in that this is founded on
--  the type-level function
--  label = λ { true → A ; false → B}, so that
--  A ⊎ B = Σ Bool label. ]

-- Recall that swap⋆equiv (from TypeEquiv) has type
-- (A × B) ≃ (B × A).  So ua would tell us that these
-- two are 'equal'.  Certainly they should be
-- indistinguishable, in the sense that there ought to be
-- no fundamental property that distinguishes them.  But
-- they are not really, fully equal, are they?  _×_ has
-- an implementation, and proj₁ / proj₂ lets you 'see'
-- a first/second component in each, and these are not
-- equal.

-- Nevertheless, equivalences of types induce some interesting
-- automorphisms.
induce : {ℓ : Level} {A B : Set ℓ} → A ≃ B → (A ⊎ B) ≃ (A × Bool)
induce {_} {A} {B} (qeq f g α β) = qeq fwd bwd fwd∘bwd∼id bwd∘fwd∼id
  where
    fwd : A ⊎ B → A × Bool
    fwd (inj₁ x) = id x , true -- explicit about how to map from A to A
    fwd (inj₂ y) = g y , false

    bwd : A × Bool → A ⊎ B
    bwd (a , true)  = inj₁ (id a)
    bwd (a , false) = inj₂ (f a)

    fwd∘bwd∼id : fwd ∘ bwd ∼ id
    fwd∘bwd∼id (a , true) = cong₂ _,_ refl refl
    fwd∘bwd∼id (a , false) = cong₂ _,_ (β a) refl

    bwd∘fwd∼id : bwd ∘ fwd ∼ id
    bwd∘fwd∼id (inj₁ x) = refl
    bwd∘fwd∼id (inj₂ y) = cong inj₂ (α y)

-- The most important aspect to 'induce' is how
-- 1) all parts of (A ≃ B) are used
-- 2) B does not appear in 'A × Bool' at all!
-- but of course, we can do the same on the other side:
induce′ : {ℓ : Level} {A B : Set ℓ} → A ≃ B → (A ⊎ B) ≃ (B × Bool)
induce′ e = induce (sym≃ e) ● swap₊equiv

-- Using this, we can get two rather interesting equivalences:
left× : {ℓ : Level} {A B : Set ℓ} → ((A × B) ⊎ (B × A)) ≃ ((A × B) × Bool)
left× = induce swap⋆equiv

right× : {ℓ : Level} {A B : Set ℓ} → ((A × B) ⊎ (B × A)) ≃ ((B × A) × Bool)
right× = induce′ swap⋆equiv
-- which can also be written as induce swap⋆equiv ● swap₊equiv

-- Another question to ask: is induce reversible?  We would have to
-- fill in the following, where the first hole needs an A → B function.
-- But this "doesn't work", as we know nothing about the actual
-- equivalence (more on that later).  Basically, the whole with 0
-- below does not seem to be fillable, essentially because we have
-- no guarantee that the Bool argument is used (in the equivalence)
-- as a signal for the tag of ⊎.
{-
rev-induce : {ℓ : Level} {A B : Set ℓ} → (A ⊎ B) ≃ (A × Bool) → A ≃ B
rev-induce {_} {A} {B} (qeq f g α β) = qeq f₁ {!!} {!!} {!!}
  where
    f₁ : A → B
    f₁ a with g (a , true) | inspect g (a , true) | g ( a , false) | inspect g (a , false)
    f₁ a | inj₁ x | [ eq ] | inj₁ x₁ | [ eq₁ ] = {! 0 !}
    f₁ a | inj₁ x | e | inj₂ y  | h = y
    f₁ a | inj₂ y | e | inj₁ x  | h = y
    f₁ a | inj₂ y | e | inj₂ y₁ | h = {! 1 !}
-}

--------------------------------------------------------------------------

-- Let's look at how function application mixes with these equivalences.

-- First the lhs of induce:
apl : {ℓ ℓ′ : Level} {A B : Set ℓ} {C : Set ℓ′} → (A × B → C) → ((A × B) ⊎ (B × A)) → C
apl f (inj₁ x) = f (id    x)
apl f (inj₂ y) = f (swap⋆ y)

-- and now the rhs.  Note how b : Bool is completely ignored.
apr : {ℓ ℓ′ : Level} {A B : Set ℓ} {C : Set ℓ′} → (A × B → C) → ((A × B) × Bool) → C
apr f (x , b) = f x

-- But are they the same?  Yes, they are.
the-same : {ℓ ℓ′ : Level} {A B : Set ℓ} {C : Set ℓ′} → (f : A × B → C) → (v : (A × B) ⊎ (B × A))
  → apl f v ≡ apr f ((_≃_.f left×) v)
the-same f (inj₁ x) = refl
the-same f (inj₂ y) = refl

-- In fact, this generalizes to the dependent setting, with a little care.
-- Go to ------ if you don't care about this mass of code.
dispatch : {ℓ ℓ′ : Level} {A B : Set ℓ} (C : A → B → Set ℓ′) → ((A × B) ⊎ (B × A)) → Set ℓ′
dispatch C (inj₁ (x , y)) = C x y
dispatch C (inj₂ (y , x)) = C x y

aplD : {ℓ ℓ′ : Level} {A B : Set ℓ} {C : A → B → Set ℓ′} → ((x : A × B) → C (proj₁ x) (proj₂ x)) → (v : (A × B) ⊎ (B × A)) → dispatch C v
aplD f (inj₁ x) = f (id    x)
aplD f (inj₂ y) = f (swap⋆ y)

aprD : {ℓ ℓ′ : Level} {A B : Set ℓ} {C : A → B → Set ℓ′} → ((x : A × B) → C (proj₁ x) (proj₂ x)) → (y : (A × B) × Bool) → C (proj₁ (proj₁ y)) (proj₂ (proj₁ y))
aprD f (x , b) = f x

map-types : {ℓ ℓ′ : Level} {A B : Set ℓ} {C : A → B → Set ℓ′} → (v : (A × B) ⊎ (B × A)) →
  let z = (_≃_.f left×) v in dispatch C v ≡ C (proj₁ (proj₁ z)) (proj₂ (proj₁ z))
map-types (inj₁ x) = refl
map-types (inj₂ y) = refl

-- So this tweak of subst seems to be the most useful way of saying how to
-- evaluate the types to show they are equal.
substD : {ℓ ℓ′ ℓ″ : Level} {A B : Set ℓ} {I : Set ℓ′}
  {T₁ : I → Set ℓ″} {T₂ : I → Set ℓ″}
  (eq : {w : I} → T₁ w ≡ T₂ w) (v : I) → T₁ v → T₂ v
substD eq v z = subst id (eq {v}) z

the-sameD : {ℓ ℓ′ : Level} {A B : Set ℓ} {C : A → B → Set ℓ′} → (f : (x : A × B) → C (proj₁ x) (proj₂ x) ) → (v : (A × B) ⊎ (B × A))
  → substD {A = A} {B} {I = (A × B) ⊎ (B × A)} (map-types v) v (aplD f v) ≡ aprD f ((_≃_.f left×) v)
the-sameD f (inj₁ x) = refl
the-sameD f (inj₂ y) = refl

------------------------------------------------------------------------

-- So what does univalence say?  One interpretation is that if A ≃ B, then
-- you can never tell A from B apart.  Actually, that interpretation is weaker
-- than full univalence, which says something positive (rather than the above
-- double negative).  But here, let's go a little bit short of full univalence,
-- and instead say that if A ≃ B, then (A ⊎ B) ≃ (A × Bool) is actually
-- quite special, and the map from the left to the right does not
-- involve the Bool other than to choose the label.  Which is, of course,
-- exactly what 'induce' gives.

-- To go from there to A ≡ B, is also to say that (A ⊎ A) ≃ A × Bool
-- (yes, that is two A, since A ≡ B).

-- [Need to continue here]
