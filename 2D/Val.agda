{-# OPTIONS --without-K #-}

module 2D.Val where

open import Data.Integer as ℤ
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (Σ) renaming (_,_ to _&_)

open import 2D.Types
open import 2D.Iter
open import 2D.Power

-- a fraction p ÷ q is a way of identifying r such that p ^ i ◎ ! q ^ j ⇔ r
-- or (equivalently) p ^ i ⇔ r ◎ q ^ j.
_÷_ : {τ : U} (p q : τ ⟷ τ) → Set
_÷_ {τ} p q = (pi : Iter p) → (qj : Iter q) → Σ (τ ⟷ τ) (λ r → Iter.q pi ⇔ r ◎ Iter.q qj)

-- the "identity" tangle:
c÷c : {τ : U} (c : τ ⟷ τ) → c ÷ c
c÷c {_} c < i , p , α > < j , q , β > =
  c ^ (i ℤ.+ (ℤ.- j)) &
  α ● 2! (lower i (ℤ.- j) ⊡ β ● assoc◎r ● id⇔ ⊡ (^⇔! j) ⊡ id⇔ ● id⇔ ⊡ rinv◎l ● idr◎l)

data Val : (τ : U) → Set where
  ⋆ :       Val 𝟙
  inl :     {τ₁ τ₂ : U} → Val τ₁ → Val (τ₁ ⊕ τ₂)
  inr :     {τ₁ τ₂ : U} → Val τ₂ → Val (τ₁ ⊕ τ₂)
  [_,_] :   {τ₁ τ₂ : U} → Val τ₁ → Val τ₂ → Val (τ₁ ⊗ τ₂)
  comb :    {τ : U} {p : τ ⟷ τ} → Iter p →  Val (# p)
  tangr :   {τ : U} {p q : τ ⟷ τ} → p ÷ q → Val (p // q)
  tangl :   {τ : U} {q p : τ ⟷ τ} → p ÷ q → Val (q \\ p)

get-q : {t : U} {p : t ⟷ t} → Val (# p) → t ⟷ t
get-q (comb i) = Iter.q i

get-iter : {t : U} {p : t ⟷ t} → Val (# p) → Iter p
get-iter (comb i) = i

get// : {t : U} {p q : t ⟷ t} → Val (p // q) → p ÷ q
get// (tangr x) = x

get\\ : {t : U} {p q : t ⟷ t} → Val (q \\ p) → p ÷ q
get\\ (tangl x) = x

π₁ : {s t : U} → Val (s ⊗ t) → Val s
π₁ [ x , _ ] = x
π₂ : {s t : U} → Val (s ⊗ t) → Val t
π₂ [ _ , y ] = y

-- we also have some amount of "proof irrelevance" in some situations.  Below is the reason.
-- Basically: given p ÷ p, applied to the same p ^ i, will always give back something which
-- is equivalent to the identity.  So we can safely throw it out.
⇔-irr : {τ : U} {p : τ ⟷ τ} → (p÷p : p ÷ p) → ∀ (pi : Iter p) → Σ.proj₁ (p÷p pi pi) ⇔ Prim id⟷
⇔-irr p÷p pi = let div = p÷p pi pi in let r = Σ.proj₁ div in let pf = Σ.proj₂ div in
  (idr◎r ● id⇔ ⊡ linv◎r ● assoc◎l) ● 2! pf ⊡ id⇔ {c = ! (Iter.q pi)} ● linv◎l

mutual
  inj-eq : {s t : U} (v₁ v₂ : Val (s ⊕ t)) → Set
  inj-eq (inl v) (inl w) = v ≈ w
  inj-eq (inl v) (inr w) = ⊥
  inj-eq (inr v) (inl w) = ⊥
  inj-eq (inr v) (inr w) = v ≈ w

  data _≈_ : {t : U} → Val t → Val t → Set where
    ⋆≈  : {e f : Val 𝟙} → e ≈ f
         -- programs are equivalent when they are.. (which also means they are inverses)
    #p≈ : ∀ {t} {p : t ⟷ t} {p^i p^j : Val (# p)} →
          get-q p^i ⇔ get-q p^j → p^i ≈ p^j
    [,]≈ : {s t : U} {v₁ v₂ : Val (s ⊗ t)} → π₁ v₁ ≈ π₁ v₂ → π₂ v₁ ≈ π₂ v₂ → v₁ ≈ v₂
    inj≈ : {s t : U} → {v₁ v₂ : Val (s ⊕ t)} → inj-eq v₁ v₂ → v₁ ≈ v₂
    tangr≈ : {τ : U} {p q : τ ⟷ τ} → {f g : Val (p // q)} →
      (∀ {x : Iter p} {y : Iter q} → Σ.proj₁ (get// f x y) ⇔ Σ.proj₁ (get// g x y)) → f ≈ g
    tangl≈ : {τ : U} {q p : τ ⟷ τ} → {f g : Val (q \\ p)} →
      (∀ {x : Iter p} {y : Iter q} → Σ.proj₁ (get\\ f x y) ⇔ Σ.proj₁ (get\\ g x y)) → f ≈ g

get-equiv : ∀ {t} {p : t ⟷ t} {p^i p^j : Val (# p)} → p^i ≈ p^j → get-q p^i ⇔ get-q p^j
get-equiv (#p≈ x) = x

refl≈ : ∀ {t} {v w : Val t} → v ≡ w → v ≈ w
refl≈ {v = ⋆} refl = ⋆≈
refl≈ {v = inl v} refl = inj≈ (refl≈ refl)
refl≈ {v = inr v} refl = inj≈ (refl≈ refl)
refl≈ {v = [ v , w ]} refl = [,]≈ (refl≈ refl) (refl≈ refl)
refl≈ {v = comb q } refl = #p≈ id⇔
refl≈ {v = tangr f } refl = tangr≈ id⇔
refl≈ {v = tangl f } refl = tangl≈ id⇔

trans≈ : {t : U} → {a b c : Val t} → a ≈ b → b ≈ c → a ≈ c
trans≈ ⋆≈ ⋆≈ = ⋆≈
trans≈ (#p≈ x) (#p≈ x₁) = #p≈ (x ● x₁)
trans≈ ([,]≈ eq₁ eq₂) ([,]≈ eq₃ eq₄) = [,]≈ (trans≈ eq₁ eq₃) (trans≈ eq₂ eq₄)
trans≈ (inj≈ {v₁ = inl v₁} {inl v₂} eq₁) (inj≈ {v₂ = inl v₃} eq₂) = inj≈ (trans≈ eq₁ eq₂)
trans≈ (inj≈ {v₁ = inl v₁} {inl v₂} eq₁) (inj≈ {v₂ = inr v₃} ())
trans≈ (inj≈ {v₁ = inl v₁} {inr v₂} ()) (inj≈ eq₂)
trans≈ (inj≈ {v₁ = inr v₁} {inl v₂} ()) (inj≈ {v₂ = inl v₃} eq₂)
trans≈ (inj≈ {v₁ = inr v₁} {inr v₂} eq₁) (inj≈ {v₂ = inl v₃} ())
trans≈ (inj≈ {v₁ = inr v₁} {inl v₂} ()) (inj≈ {v₂ = inr v₃} eq₂)
trans≈ (inj≈ {v₁ = inr v₁} {inr v₂} eq₁) (inj≈ {v₂ = inr v₃} eq₂) = inj≈ (trans≈ eq₁ eq₂)
trans≈ (tangr≈ x) (tangr≈ y) = tangr≈ (x ● y)
trans≈ (tangl≈ x) (tangl≈ y) = tangl≈ (x ● y)

sym≈ : {t : U} → {a b : Val t} → a ≈ b → b ≈ a
sym≈ ⋆≈ = ⋆≈
sym≈ (#p≈ x) = #p≈ (2! x)
sym≈ ([,]≈ e₁ e₂) = [,]≈ (sym≈ e₁) (sym≈ e₂)
sym≈ (inj≈ {v₁ = inl v₁} {inl v₂} e) = inj≈ (sym≈ e)
sym≈ (inj≈ {v₁ = inl v₁} {inr v₂} ())
sym≈ (inj≈ {v₁ = inr v₁} {inl v₂} ())
sym≈ (inj≈ {v₁ = inr v₁} {inr v₂} e) = inj≈ (sym≈ e)
sym≈ (tangl≈ x) = tangl≈ (2! x)
sym≈ (tangr≈ x) = tangr≈ (2! x)

open import Relation.Binary

module _ {T : U} where
  ≈-setoid : Setoid _ _
  ≈-setoid = record { Carrier = Val T
                    ; _≈_ = _≈_
                    ; isEquivalence = record { refl = refl≈ refl
                                             ; sym = sym≈
                                             ; trans = trans≈ }
                    }
  module EqR where
    open import Relation.Binary.EqReasoning ≈-setoid public

-----------
-- Justifying synchr⋆ 's implementation:
--    synchr⋆ : {t : U} {p q : t ⟷ t} → (p // q) ⊗ # p ⟷ # p ⊗ (q \\ p)
synchr⋆-lemma : {t : U} {p q : t ⟷ t} → (ip : Iter p) → (x : p ÷ q) →
  ∀ (iq : Iter q) → Iter.q  ip ⇔ Σ.proj₁ (x ip iq) ◎ Iter.q iq
synchr⋆-lemma ip x iq with x ip iq
... | r & pf = pf
