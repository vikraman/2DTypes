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

CoxeterRel  : {n : ℕ} → Rel (List (Fin n)) lzero
CoxeterRel {O} = λ _ _ → ⊤
CoxeterRel {S n} = _≈₁_ {n}

syntax CoxeterRel l1 l2 = l1 ≈ l2

CoxeterRel-refl : {n : ℕ} → is-refl (CoxeterRel {n})
CoxeterRel-refl {O} = λ _ → unit
CoxeterRel-refl {S n} = λ _ → idp

CoxeterRel-sym : {n : ℕ} → is-sym (CoxeterRel {n})
CoxeterRel-sym {O} = λ _ → unit
CoxeterRel-sym {S n} = comm

CoxeterRel-trans : {n : ℕ} → is-trans (CoxeterRel {n})
CoxeterRel-trans {O} = λ _ _ → unit
CoxeterRel-trans {S n} = trans

Sn : (n : ℕ) → Type lzero
Sn n = SetQuot (CoxeterRel {n})

instance
  Sn-level : {n : ℕ} → is-set (Sn n)
  Sn-level = SetQuot-is-set

private
  list++-assoc-lemma : {n : ℕ} → (l₁ l₂ l₃ l₄ : List (Fin n)) → (l₁ ++ l₂) ++ (l₃ ++ l₄) == l₁ ++ (l₂ ++ l₃) ++ l₄
  list++-assoc-lemma l₁ l₂ l₃ l₄ = (++-assoc l₁ l₂ (l₃ ++ l₄)) ∙ ap (λ e → l₁ ++ e) (! (++-assoc l₂ l₃ l₄))

idp≃ : {n : ℕ} → (l₁ l₂ : List (Fin (S n))) → (l₁ == l₂) → (l₁ ≈ l₂)
idp≃ l₁ l₂ p = transport (λ e → l₁ ≈ e) p idp

respects-++-lr : {n : ℕ} → (l m m' r : List (Fin (S n))) → (m ≈ m') → (l ++ (m ++ r)) ≈ (l ++ (m' ++ r))
respects-++-lr l m m' r p = respects-++ {l = l} {l' = l} idp (respects-++ p idp)

≈-inv-r : {n : ℕ} → (l : List (Fin n)) → (l ++ reverse l) ≈ nil
≈-inv-r {O} l = unit
≈-inv-r {S n} nil = idp
≈-inv-r {S n} (x :: l) = 
  trans (idp≃ _ _ (list++-assoc-lemma (x :: nil) l (reverse l) (x :: nil))) 
  (trans (respects-++-lr (x :: nil) (l ++ reverse l) nil (x :: nil) (≈-inv-r l)) 
  cancel)

≈-inv-l : {n : ℕ} → (l : List (Fin n)) → ((reverse l) ++ l) ≈ nil
≈-inv-l {O} l = unit
≈-inv-l {S n} nil = idp
≈-inv-l {S n} (x :: l) = 
  trans (idp≃ _ _ (list++-assoc-lemma (reverse l) (x :: nil) (x :: nil) l)) 
  (trans (respects-++-lr (reverse l) (x :: x :: nil) nil l cancel) 
  (≈-inv-l l))