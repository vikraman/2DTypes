{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Sn where

open import lib.Base
open import lib.Relation
open import lib.PathGroupoid
open import lib.NType
open import lib.types.SetQuotient public
open import lib.types.List
open import lib.types.Fin

open import Pi+.Extra
open import Pi+.Coxeter.Coxeter
open import Pi+.Misc

CoxeterRel  : {n : ℕ} → Rel (List (Fin (S n))) lzero
CoxeterRel {O} = λ _ _ → ⊤
CoxeterRel {S O} = λ _ _ → ⊤
CoxeterRel {S (S n)} = _≈₁_ {m = S (S n)}

syntax CoxeterRel l1 l2 = l1 ≈ l2

CoxeterRel-refl : {n : ℕ} → is-refl (CoxeterRel {n})
CoxeterRel-refl {O} = λ _ → unit
CoxeterRel-refl {S O} = λ _ → unit
CoxeterRel-refl {S (S n)} = λ _ → idp

CoxeterRel-sym : {n : ℕ} → is-sym (CoxeterRel {n})
CoxeterRel-sym {O} = λ _ → unit
CoxeterRel-sym {S O} = λ _ → unit
CoxeterRel-sym {S (S n)} = comm

CoxeterRel-trans : {n : ℕ} → is-trans (CoxeterRel {n})
CoxeterRel-trans {O} = λ _ _ → unit
CoxeterRel-trans {S O} = λ _ _ → unit
CoxeterRel-trans {S (S n)} = trans

Sn : (n : ℕ) → Type lzero
Sn n = SetQuot (CoxeterRel {n})

instance
  Sn-level : {n : ℕ} → is-set (Sn n)
  Sn-level = SetQuot-is-set

private
  list++-assoc-lemma : {n : ℕ} → (l₁ l₂ l₃ l₄ : List (Fin n)) → (l₁ ++ l₂) ++ (l₃ ++ l₄) == l₁ ++ (l₂ ++ l₃) ++ l₄
  list++-assoc-lemma l₁ l₂ l₃ l₄ = (++-assoc l₁ l₂ (l₃ ++ l₄)) ∙ ap (λ e → l₁ ++ e) (! (++-assoc l₂ l₃ l₄))

idp== : {n : ℕ} → (l₁ l₂ : List (Fin (S n))) → (l₁ == l₂) → (l₁ ≈₁ l₂)
idp== {n = n} l₁ l₂ p = transport (λ e → l₁ ≈₁ e) p idp

idp≃ : {n : ℕ} → (l₁ l₂ : List (Fin (S n))) → (l₁ == l₂) → (l₁ ≈ l₂)
idp≃ {n = O} l₁ l₂ p = unit
idp≃ {n = S O} l₁ l₂ p = unit
idp≃ {n = S (S n)} = idp== 

respects-++-lr : {n : ℕ} → (l m m' r : List (Fin (S n))) → (m ≈ m') → (l ++ (m ++ r)) ≈ (l ++ (m' ++ r))
respects-++-lr {n = O} l m m' r p = unit
respects-++-lr {n = S O} l m m' r p = unit
respects-++-lr {n = S (S n)} l m m' r p = respects-++ {l = l} {l' = l} idp (respects-++ p idp)

≈-inv-r : {n : ℕ} → (l : List (Fin (S n))) → (l ++ reverse l) ≈ nil
≈-inv-r {O} l = unit
≈-inv-r {S O} l = unit
≈-inv-r {S (S n)} nil = idp
≈-inv-r {S (S n)} (x :: l) = 
  trans (idp≃ _ _ (list++-assoc-lemma (x :: nil) l (reverse l) (x :: nil)))
  (trans (respects-++-lr (x :: nil) (l ++ reverse l) nil (x :: nil) (≈-inv-r l))
  cancel)

≈-inv-l : {n : ℕ} → (l : List (Fin (S n))) → ((reverse l) ++ l) ≈ nil
≈-inv-l {O} l = unit
≈-inv-l {S O} nil = unit
≈-inv-l {S O} (_ :: _) = unit
≈-inv-l {S (S n)} nil = idp
≈-inv-l {S (S n)} (x :: l) =
  trans (idp≃ _ _ (list++-assoc-lemma (reverse l) (x :: nil) (x :: nil) l))
  (trans (respects-++-lr (reverse l) (x :: x :: nil) nil l cancel)
  (≈-inv-l l))

reverse-respects-≈₁ : {n : ℕ} {l1 l2 : List (Fin (S n))} → l1 ≈₁ l2 → reverse l1 ≈₁ reverse l2
reverse-respects-≈₁ cancel = cancel
reverse-respects-≈₁ (swap p) = comm (swap p)
reverse-respects-≈₁ braid = braid
reverse-respects-≈₁ idp = idp
reverse-respects-≈₁ (comm {l1 = l1} {l2 = l2} p) =
  comm {l1 = reverse l1} {l2 = reverse l2} (reverse-respects-≈₁ p)
reverse-respects-≈₁ (trans {l1 = l1} {l2 = l2} {l3 = l3} p1 p2) =
  let r1 = reverse-respects-≈₁ {l1 = l2} {l2 = l3} p2
      r2 = reverse-respects-≈₁ {l1 = l1} {l2 = l2} p1
  in  trans {l1 = reverse l1} {l2 = reverse l2} {l3 = reverse l3} r2 r1
reverse-respects-≈₁ (respects-++ {l = l} {l' = l'} {r = r} {r' = r'} p1 p2) =
  let r1 = reverse-respects-≈₁ p1
      r2 = reverse-respects-≈₁ p2
      s1 = reverse-++ l r
      s2 = reverse-++ l' r'
  in  trans (idp== _ _ s1) (trans (respects-++ r2 r1) (idp== _ _ (! s2)))

reverse-respects-≈ : {n : ℕ} {l1 l2 : List (Fin (S n))} → l1 ≈ l2 → reverse l1 ≈ reverse l2
reverse-respects-≈ {O} unit = unit
reverse-respects-≈ {S O} unit = unit
reverse-respects-≈ {S (S n)} p = reverse-respects-≈₁ p

++-respects-≈ : {n : ℕ} {l1 l2 r1 r2 : List (Fin (S n))} → l1 ≈ l2 → r1 ≈ r2 → (l1 ++ r1) ≈ (l2 ++ r2)
++-respects-≈ {n = O} p1 p2 = unit
++-respects-≈ {n = S O} p1 p2 = unit
++-respects-≈ {n = S (S n)} p1 p2 = respects-++ p1 p2

::-respects-≈ : {n : ℕ} {x : Fin (S n)} {l1 l2 : List (Fin (S n))} → l1 ≈ l2 → (x :: l1) ≈ (x :: l2)
::-respects-≈ {n = O} p = unit
::-respects-≈ {n = S O} p = unit
::-respects-≈ {n = S (S n)} p = respects-++ idp p
