{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

module Pi+.Coxeter.Sn where

open import lib.Base
open import lib.Relation
open import lib.PathGroupoid
open import lib.Function
open import lib.Function2
open import lib.NType
open import lib.NType2
open import lib.types.SetQuotient public
open import lib.types.List
open import lib.types.Fin
open import lib.types.Truncation

open import Pi+.Extra
open import Pi+.Coxeter.Coxeter
open import Pi+.Coxeter.NonParametrized.LehmerCanonical
open import Pi+.Misc

Sn : (n : ℕ) → Type lzero
Sn n = SetQuot (_≈*_ {n})

instance
  Sn-level : {n : ℕ} → is-set (Sn n)
  Sn-level = SetQuot-is-set

private
  list++-assoc-lemma : {n : ℕ} → (l₁ l₂ l₃ l₄ : List (Fin n)) → (l₁ ++ l₂) ++ (l₃ ++ l₄) == l₁ ++ (l₂ ++ l₃) ++ l₄
  list++-assoc-lemma l₁ l₂ l₃ l₄ = (++-assoc l₁ l₂ (l₃ ++ l₄)) ∙ ap (λ e → l₁ ++ e) (! (++-assoc l₂ l₃ l₄))

idp≃ : {n : ℕ} → (l₁ l₂ : List (Fin n)) → (l₁ == l₂) → (l₁ ≈* l₂)
idp≃ l₁ l₂ p = transport (λ e → l₁ ≈* e) p idp

respects-++-lr : {n : ℕ} → (l m m' r : List (Fin (S n))) → (m ≈* m') → (l ++ (m ++ r)) ≈* (l ++ (m' ++ r))
respects-++-lr l m m' r p = respects-++ {l = l} {l' = l} idp (respects-++ p idp)

≈-inv-r : {n : ℕ} → (l : List (Fin n)) → (l ++ reverse l) ≈* nil
≈-inv-r {O} nil = idp
≈-inv-r {S n} nil = idp
≈-inv-r {S n} (x :: l) =
  trans (idp≃ _ _ (list++-assoc-lemma (x :: nil) l (reverse l) (x :: nil)))
  (trans (respects-++-lr (x :: nil) (l ++ reverse l) nil (x :: nil) (≈-inv-r l))
  (≈-rel cancel))

≈-inv-l : {n : ℕ} → (l : List (Fin n)) → ((reverse l) ++ l) ≈* nil
≈-inv-l {O} nil = idp
≈-inv-l {S n} nil = idp
≈-inv-l {S n} (x :: l) =
  trans (idp≃ _ _ (list++-assoc-lemma (reverse l) (x :: nil) (x :: nil) l))
  (trans (respects-++-lr (reverse l) (x :: x :: nil) nil l (≈-rel cancel))
  (≈-inv-l l))

reverse-respects-≈ : {n : ℕ} {l1 l2 : List (Fin n)} → l1 ≈* l2 → reverse l1 ≈* reverse l2
reverse-respects-≈ {O} {nil} {nil} p = p
reverse-respects-≈ {S n} (≈-rel cancel) = (≈-rel cancel)
reverse-respects-≈ {S n} (≈-rel (swap p)) = comm (≈-rel (swap p))
reverse-respects-≈ {S n} (≈-rel braid) = ≈-rel braid
reverse-respects-≈ {S n} idp = idp
reverse-respects-≈ {S n} (comm {l1 = l1} {l2 = l2} p) =
  comm {l1 = reverse l1} {l2 = reverse l2} (reverse-respects-≈ p)
reverse-respects-≈ {S n} (trans {l1 = l1} {l2 = l2} {l3 = l3} p1 p2) =
  let r1 = reverse-respects-≈ {l1 = l2} {l2 = l3} p2
      r2 = reverse-respects-≈ {l1 = l1} {l2 = l2} p1
  in  trans {l1 = reverse l1} {l2 = reverse l2} {l3 = reverse l3} r2 r1
reverse-respects-≈ {S n} (respects-++ {l = l} {l' = l'} {r = r} {r' = r'} p1 p2) =
  let r1 = reverse-respects-≈ p1
      r2 = reverse-respects-≈ p2
      s1 = reverse-++ l r
      s2 = reverse-++ l' r'
  in  trans (idp≃ _ _ s1) (trans (respects-++ r2 r1) (idp≃ _ _ (! s2)))

::-respects-≈ : {n : ℕ} {x : Fin n} {l1 l2 : List (Fin n)} → l1 ≈* l2 → (x :: l1) ≈* (x :: l2)
::-respects-≈ {n = S n} p = respects-++ idp p

open import Pi+.Coxeter.LehmerCoxeterEquiv

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

  -- not a proposition, or is retraction

  has-section : (f : A → B) → Type (lmax i j)
  has-section f = Σ (B → A) (λ g → f ∘ g ∼ idf B)

  has-hfiber-is-retract : {f : A → B} → ((b : B) → hfiber f b) → has-section f
  has-hfiber-is-retract h = fst ∘ h , snd ∘ h

  im : (f : A → B) → Type (lmax i j)
  im f = Σ B (λ b → hfiber f b)

  restrict : (f : A → B) → A → im f
  restrict f a = f a , a , idp

restrict-is-retract : ∀ {i j} {A : Type i} {B : Type j} {f : A → B} → has-section (restrict f)
restrict-is-retract {f = f} = (λ { (b , a , p) → a }) , λ { (.(f a) , a , idp) → idp }

module _ {i} {A : Type i} where

  is-idempotent : (f : A → A) → Type i
  is-idempotent f = (f ∘ f) ∼ f

q-norm-has-section : {n : ℕ} → has-section (q[_] ∘ norm {n})
q-norm-has-section =
  norm-inc , SetQuot-elim (λ w → quot-rel (comm (norm-≈* w ■ norm-≈* (norm w))))
                          (λ r → prop-has-all-paths-↓)

is-norm : {n : ℕ} → List (Fin n) → Type₀
is-norm l = norm l == l

module _ {i} {A : Type i} {j} {R : Rel A j} where

  q-is-surj : is-surj (q[_] {R = R})
  q-is-surj =
    SetQuot-elim ⦃ raise-level _ Trunc-level ⦄
      (λ a → [ a , idp ]) λ r → prop-has-all-paths-↓

norm-q-is-surj : {n : ℕ} → is-surj (q[_] {R = _≈*_})
norm-q-is-surj {n} w = [ norm-inc {n} w , norm-inc-right-inv w ]
