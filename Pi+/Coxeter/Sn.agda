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

Sn : (n : ℕ) → Type lzero
Sn n = SetQuot (_≈*_ {n})

instance
  Sn-level : {n : ℕ} → is-set (Sn n)
  Sn-level = SetQuot-is-set

private
  list++-assoc-lemma : {n : ℕ} → (l₁ l₂ l₃ l₄ : List (Fin n)) → (l₁ ++ l₂) ++ (l₃ ++ l₄) == l₁ ++ (l₂ ++ l₃) ++ l₄
  list++-assoc-lemma l₁ l₂ l₃ l₄ = (++-assoc l₁ l₂ (l₃ ++ l₄)) ∙ ap (λ e → l₁ ++ e) (! (++-assoc l₂ l₃ l₄))

idp≃ : {n : ℕ} → (l₁ l₂ : List (Fin (S n))) → (l₁ == l₂) → (l₁ ≈* l₂)
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
