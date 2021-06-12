{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Sn2 where

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
Sn n = SetQuot (_≈∗_ {m = n})

instance
  Sn-level : {n : ℕ} → is-set (Sn n)
  Sn-level = SetQuot-is-set

private
  list++-assoc-lemma : {n : ℕ} → (l₁ l₂ l₃ l₄ : List (Fin n)) → (l₁ ++ l₂) ++ (l₃ ++ l₄) == l₁ ++ (l₂ ++ l₃) ++ l₄
  list++-assoc-lemma l₁ l₂ l₃ l₄ = (++-assoc l₁ l₂ (l₃ ++ l₄)) ∙ ap (λ e → l₁ ++ e) (! (++-assoc l₂ l₃ l₄))

idp== : {n : ℕ} → (l l₂ : List (Fin n)) → (l == l₂) → (l ≈∗ l₂)
idp== {n = n} l l₂ p = transport (λ e → l ≈∗ e) p idp

respects-++-lr : {n : ℕ} → (l m m' r : List (Fin n)) → (m ≈∗ m') → (l ++ (m ++ r)) ≈∗ (l ++ (m' ++ r))
respects-++-lr l m m' r p =
  respects-++ {l = l} {l} {m ++ r} {m' ++ r} idp
              (respects-++ {l = m} {m'} {r} {r} p idp)

≈-inv-r : {n : ℕ} → (l : List (Fin n)) → (l ++ reverse l) ≈∗ nil
≈-inv-r nil = idp
≈-inv-r (x :: l) =
  idp== _ _ (list++-assoc-lemma (x :: nil) l (reverse l) (x :: nil)) ■
  respects-++-lr (x :: nil) (l ++ reverse l) nil (x :: nil) (≈-inv-r l) ■
  cancel

≈-inv-l : {n : ℕ} → (l : List (Fin n)) → ((reverse l) ++ l) ≈∗ nil
≈-inv-l nil = idp
≈-inv-l (x :: l) =
  idp== _ _ (list++-assoc-lemma (reverse l) (x :: nil) (x :: nil) l) ■
  respects-++-lr (reverse l) (x :: x :: nil) nil l cancel ■
  ≈-inv-l l

reverse-respects-≈∗ : {n : ℕ} {l1 l2 : List (Fin n)} → l1 ≈∗ l2 → reverse l1 ≈∗ reverse l2
reverse-respects-≈∗ cancel = cancel
reverse-respects-≈∗ idp = idp
reverse-respects-≈∗ (comm p) =
  comm (reverse-respects-≈∗ p)
reverse-respects-≈∗ (trans p1 p2) =
  trans (reverse-respects-≈∗ p1) (reverse-respects-≈∗ p2)
reverse-respects-≈∗ (respects-++ {l = l} {l' = l'} {r = r} {r' = r'} p1 p2) =
  idp== _ _ (reverse-++ l r) ■
  respects-++ (reverse-respects-≈∗ p2) (reverse-respects-≈∗ p1) ■
  idp== _ _ (! (reverse-++ l' r'))
reverse-respects-≈∗ (≈-rel (swap p)) = comm (≈-rel (swap p))
reverse-respects-≈∗ (≈-rel braid) = ≈-rel braid

++-respects-≈∗ : {n : ℕ} {l1 l2 r1 r2 : List (Fin n)} → l1 ≈∗ l2 → r1 ≈∗ r2 → (l1 ++ r1) ≈∗ (l2 ++ r2)
++-respects-≈∗ p1 p2 = respects-++ p1 p2

::-respects-≈∗ : {n : ℕ} {x : Fin n} {l1 l2 : List (Fin n)} → l1 ≈∗ l2 → (x :: l1) ≈∗ (x :: l2)
::-respects-≈∗ p = ++-respects-≈∗ idp p
