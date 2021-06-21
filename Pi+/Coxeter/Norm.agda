{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

module Pi+.Coxeter.Norm where

open import HoTT

open import Pi+.Coxeter.Sn
open import Pi+.Coxeter.Coxeter
open import Pi+.Coxeter.LehmerCoxeterEquiv

open import Pi+.Extra
open import Pi+.Misc

norm : {n : ℕ} → (l : List (Fin n)) → List (Fin n)
norm {O} nil = nil
norm {S n} l = immersion code
  where code = ListFin-to-Lehmer l .fst

norm-≈* : {n : ℕ} → (l : List (Fin n)) → l ≈* norm l
norm-≈* {O} nil = idp
norm-≈* {S n} l = code≈*
  where code = ListFin-to-Lehmer l .fst
        code≈* = ListFin-to-Lehmer l .snd

norm-norm : {n : ℕ} → (l : List (Fin n)) → norm l == norm (norm l)
norm-norm {O} nil = idp
norm-norm {S n} l =
  let z = immersion-is-injection (immersion⁻¹ l) ((immersion⁻¹ (norm l))) (norm-≈* (norm l))
  in ap immersion z

≈*-norm : {n : ℕ} {l1 l2 : List (Fin n)} → l1 ≈* l2 → norm l1 == norm l2
≈*-norm {O} {nil} {nil} r = idp
≈*-norm {S n} {l1} {l2} r = ap immersion (immersion⁻¹-respects≈ r)

instance
  List-level : ∀ {n} {i} {A : Type i} → {{_ : has-level n A}} → has-level n (List A)
  List-level = TODO-

norm-inc : {n : ℕ} → Sn n → List (Fin n)
norm-inc w =
  SetQuot-rec ⦃ List-level {{Fin-is-set}} ⦄ norm ≈*-norm w

norm-inc-right-inv : {n : ℕ} (w : Sn n) → q[ norm-inc w ] == w
norm-inc-right-inv =
  SetQuot-elim (λ l → quot-rel (comm (norm-≈* l))) λ r → prop-has-all-paths-↓

module _ {i j} {A : Type i} {B : Type j} where

  has-section : (f : A → B) → Type (lmax i j)
  has-section f = Σ (B → A) (λ g → f ∘ g ∼ idf B)

  has-hfiber-has-section : {f : A → B} → ((b : B) → hfiber f b) → has-section f
  has-hfiber-has-section h = fst ∘ h , snd ∘ h

module _ {i j} {A : Type i} {B : Type j} where

  im : (f : A → B) → Type (lmax i j)
  im f = Σ B (λ b → hfiber f b)

  restrict : (f : A → B) → A → im f
  restrict f a = f a , a , idp

  restrict-is-retract : {f : A → B} → has-section (restrict f)
  restrict-is-retract {f} = (λ { (b , a , p) → a }) , (λ { (.(f a) , a , idp) → idp })

module _ {i j} {A : Type i} {B : Type j} where

  has-retraction : (f : A → B) → Type (lmax i j)
  has-retraction f = Σ (B → A) (λ g → g ∘ f ∼ idf A)

module _ {i j} {B : Type j} where

  is-retract : Type i → Type (lmax i j)
  is-retract A = Σ (A → B) (λ i → Σ (B → A) λ r → r ∘ i ∼ idf A )

module _ {i} {A : Type i} where

  is-idempotent : (f : A → A) → Type i
  is-idempotent f = (f ∘ f) ∼ f

  is-split-idempotent : (f : A → A) → Type (lsucc i)
  is-split-idempotent f =
    is-idempotent f × Σ (Type i) (λ B → Σ (A → B) (λ r → Σ (B → A) (λ s → (s ∘ r ∼ f) × (r ∘ s ∼ idf B))))

q-norm-has-section : {n : ℕ} → has-section (q[_] ∘ norm {n})
q-norm-has-section =
  norm-inc , SetQuot-elim (λ w → quot-rel (comm (norm-≈* w ■ norm-≈* (norm w))))
                          (λ r → prop-has-all-paths-↓)

norm-is-idempotent : {n : ℕ} → is-idempotent (norm {n})
norm-is-idempotent l = ! (norm-norm l)

norm-is-split-idempotent : {n : ℕ} → is-split-idempotent norm
norm-is-split-idempotent {n} =
  norm-is-idempotent , Sn n , q[_] , norm-inc , (λ l → idp) , norm-inc-right-inv

Sn-is-retract : {n : ℕ} → is-retract (Sn n)
Sn-is-retract =
  norm-inc , q[_] ,
  SetQuot-elim (λ l → quot-rel (comm (norm-≈* l))) λ r → prop-has-all-paths-↓

Sn-is-retract2 : {n : ℕ} → is-retract (Sn n)
Sn-is-retract2 =
  norm-inc , q[_] ∘ norm ,
  SetQuot-elim (λ l → ! (quot-rel (norm-≈* l) ∙ quot-rel (norm-≈* (norm l)))) λ r → prop-has-all-paths-↓

is-norm : {n : ℕ} → List (Fin n) → Type₀
is-norm l = norm l == l

module _ {i} {A : Type i} {j} {R : Rel A j} where

  q-is-surj : is-surj (q[_] {R = R})
  q-is-surj =
    SetQuot-elim ⦃ raise-level _ Trunc-level ⦄
      (λ a → [ a , idp ]) λ r → prop-has-all-paths-↓

norm-q-is-surj : {n : ℕ} → is-surj (q[_] {R = _≈*_})
norm-q-is-surj {n} w = [ norm-inc {n} w , norm-inc-right-inv w ]
