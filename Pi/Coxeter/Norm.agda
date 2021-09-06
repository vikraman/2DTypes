{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

module Pi.Coxeter.Norm where

open import HoTT

open import Pi.Coxeter.Sn
open import Pi.Coxeter.Coxeter
open import Pi.Coxeter.LehmerCoxeterEquiv

open import Pi.Extra
open import Pi.Misc

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

  im : (n : ℕ₋₂) (f : A → B) → Type (lmax i j)
  im n f = Σ B (λ b → Trunc n (hfiber f b))

  restrict : {n : ℕ₋₂} (f : A → B) → A → im n f
  restrict f a = f a , [ a , idp ]

  restrict-has-section : {n : ℕ₋₂} {{_ : has-level n A}} {{_ : has-level (S n) B}} {f : A → B}
                       → has-section (restrict {n = n} f)
  restrict-has-section {n} {f} = s , s-is-section
    where s : im n f → A
          s (b , ϕ) = Trunc-rec fst ϕ
          s-is-section : restrict f ∘ s ∼ idf (im n f)
          s-is-section (b , ϕ) =
            Trunc-elim {P = λ ψ → (restrict f ∘ s) (b , ψ) == idf (im n f) (b , ψ)}
                       {{λ {x} → has-level-apply-instance {{Σ-level ⟨⟩ λ _ → raise-level _ ⟨⟩}}}}
                       (λ { (a , idp) → idp }) ϕ

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

  SetQuot≃im-q : SetQuot R ≃ im -1 (q[_] {R = R})
  SetQuot≃im-q = equiv f g f-g g-f
    where f : SetQuot R → im -1 q[_]
          f = SetQuot-rec ⦃ Σ-level-instance {{⟨⟩}} {{raise-level _ ⟨⟩}} ⦄
                          (λ a → q[ a ] , [ a , idp ])
                          (λ r → pair= (quot-rel r) prop-has-all-paths-↓)
          g : im -1 q[_] → SetQuot R
          g = fst
          f-g : (x : im (S ⟨-2⟩) q[_]) → f (g x) == x
          f-g (x , ϕ) = Trunc-elim {P = λ ψ → f (g (x , ψ)) == x , ψ}
                                   ⦃ has-level-apply (Σ-level-instance {{⟨⟩}} {{raise-level _ ⟨⟩}}) _ _ ⦄
                                   (λ { (a , idp) → idp }) ϕ
          g-f : (x : SetQuot R) → g (f x) == x
          g-f = SetQuot-elim (λ a → idp) (λ r → prop-has-all-paths-↓)

norm-q-is-surj : {n : ℕ} → is-surj (q[_] {R = _≈*_})
norm-q-is-surj {n} w = [ norm-inc {n} w , norm-inc-right-inv w ]

Sn≃im-q-norm : {n : ℕ} → Sn n ≃ im -1 ((q[_] {R = _≈*_}) ∘ norm {n})
Sn≃im-q-norm = transport-equiv (im -1) (λ= (quot-rel ∘ norm-≈*)) ∘e SetQuot≃im-q

Sn≃im-norm : {n : ℕ} → Sn n ≃ im -1 (norm {n})
Sn≃im-norm {n} = equiv f g f-g g-f
  where instance _ = Fin-is-set
        f : Sn n → im -1 (norm {n})
        f = SetQuot-rec ⦃ Σ-level-instance {{⟨⟩}} {{raise-level _ ⟨⟩}} ⦄
                        (λ w → norm w , [ w , idp ])
                        (λ r → pair= (≈*-norm r) prop-has-all-paths-↓)
        g : im -1 (norm {n}) → Sn n
        g (l , ϕ) = q[ l ]
        f-g : (x : im -1 norm) → f (g x) == x
        f-g (l , ϕ) = Trunc-elim {P = λ ψ → f (g (l , ψ)) == l , ψ}
                                 ⦃ has-level-apply (Σ-level-instance {{⟨⟩}} {{raise-level _ ⟨⟩}}) _ _ ⦄
                                 (λ { (w , ψ) → pair= (! (norm-norm w ∙ ap norm ψ) ∙ ψ) prop-has-all-paths-↓ }) ϕ
        g-f : (x : Sn n) → g (f x) == x
        g-f = SetQuot-elim (λ l → quot-rel (comm (norm-≈* l)))
                           (λ r → prop-has-all-paths-↓)

im-q-im-norm : {n : ℕ} → im -1 (q[_] {R = _≈*_}) ≃ im -1 (norm {n})
im-q-im-norm {n} = Sn≃im-norm ∘e  SetQuot≃im-q ⁻¹
