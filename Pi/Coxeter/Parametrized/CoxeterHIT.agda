{-# OPTIONS --without-K --rewriting #-}

module Pi.Coxeter.Parametrized.CoxeterHIT where

open import lib.Base
open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.PathOver
open import lib.types.Nat
open import lib.types.Sigma
open import lib.PathGroupoid
open import lib.Funext
open import lib.types.Pi
open import lib.types.Fin

⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
⟨_⟩ = Fin-S

S⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
S⟨ k , kltn ⟩ = S k , <-ap-S kltn

infixr 35 _::_

postulate
  CList : ℕ → Type₀
  nil : ∀ {m} → CList m
  _::_ : ∀ {m} → Fin (S m) → CList m → CList m

  cancel : ∀ {m} → {n : Fin (S m)} {w : CList m} → (n :: n :: w) == w
  swap : ∀ {m} → {n : Fin (S m)} {k : Fin (S m)} → (S (k .fst) < (n .fst)) → {w : CList m} → (n :: k :: w) == (k :: n :: w)
  braid : ∀ {m} → {n : Fin m} {w : CList m} → (S⟨ n ⟩ :: ⟨ n ⟩ :: S⟨ n ⟩ :: w) == (⟨ n ⟩ :: S⟨ n ⟩ :: ⟨ n ⟩ :: w)

  instance trunc : ∀ {m} → is-set (CList m)

[_] : ∀ {m} → Fin (S m) → CList m
[ n ] = n :: nil

module CListElim {i} {m} {P : CList m → Type i}
  (nil* : P nil)
  (_::*_ : (n : Fin (S m)) {w : CList m} (w* : P w) → P (n :: w))
  (cancel* : {n : Fin (S m)} {w : CList m} {w* : P w} → (n ::* (n ::* w*)) == w* [ P ↓ cancel ])
  (swap* : {n : Fin (S m)} {k : Fin (S m)} → (p : S (k .fst) < (n .fst)) → {w : CList m} {w* : P w} → (n ::* (k ::* w*)) == (k ::* (n ::* w*)) [ P ↓ swap p ])
  (braid* : {n : Fin m} {w : CList m} {w* : P w} → (S⟨ n ⟩ ::* (⟨ n ⟩ ::* (S⟨ n ⟩ ::* w*))) == (⟨ n ⟩ ::* (S⟨ n ⟩ ::* (⟨ n ⟩ ::* w*))) [ P ↓ braid ])
  {{trunc* : {w : CList m} → is-set (P w)}}
  where

  postulate
    f : (w : CList m) → P w
    f-nil-β : f nil ↦ nil*
    {-# REWRITE f-nil-β #-}
    f-::-β : {n : Fin (S m)} {w : CList m} → f (n :: w) ↦ (n ::* (f w))
    {-# REWRITE f-::-β #-}

  postulate
    f-cancel-β : {n : Fin (S m)} {w : CList m} → apd f (cancel {m} {n} {w}) == cancel* {n} {w}
    f-swap-β : {n : Fin (S m)} {k : Fin (S m)} {w : CList m} → (p : S (k .fst) < (n .fst)) → apd f (swap {m} {n} {k} p {w}) == swap* p {w}
    f-braid-β : {n : Fin m} {w : CList m} → apd f (braid {m} {n} {w}) == braid* {n} {w}

module CListElimProp {i} {m} {P : CList m → Type i}
  (nil* : P nil)
  (_::*_ : (n : Fin (S m)) {w : CList m} (w* : P w) → P (n :: w))
  {{trunc* : {w : CList m} → is-prop (P w)}}
  where
  private module E = CListElim {P = P} nil* _::*_ prop-has-all-paths-↓ (λ p → prop-has-all-paths-↓) prop-has-all-paths-↓
  f : (w : CList m) → P w
  f = E.f {{raise-level -1 trunc*}}

module CListRec {i} {m} {P : Type i}
  (nil* : P)
  (_::*_ : (n : Fin (S m)) (w* : P) → P)
  (cancel* : {n : Fin (S m)} {w* : P} → (n ::* (n ::* w*)) == w*)
  (swap* : {n : Fin (S m)} {k : Fin (S m)} → (p : S (k .fst) < (n .fst)) → {w* : P} → (n ::* (k ::* w*)) == (k ::* (n ::* w*)))
  (braid* : {n : Fin m} {w* : P} → (S⟨ n ⟩ ::* (⟨ n ⟩ ::* (S⟨ n ⟩ ::* w*))) == (⟨ n ⟩ ::* (S⟨ n ⟩ ::* (⟨ n ⟩ ::* w*))))
  {{trunc* : is-set P}}
  where

  private module E = CListElim {P = λ _ → P} nil* (λ n p → n ::* p) (↓-cst-in cancel*) (λ p → ↓-cst-in (swap* p)) (↓-cst-in braid*)

  f : CList m → P
  f = E.f

  f-cancel-β : {n : Fin (S m)} {w : CList m} → ap f (cancel {m} {n} {w}) == cancel* {n} {f w}
  f-cancel-β = apd=cst-in E.f-cancel-β

  f-swap-β : {n : Fin (S m)} {k : Fin (S m)} → (p : S (k .fst) < (n .fst)) {w : CList m} → ap f (swap {m} {n} {k} p {w}) == swap* p {f w}
  f-swap-β p = apd=cst-in (E.f-swap-β p)

  f-braid-β : {n : Fin m} {w : CList m} → ap f (braid {m} {n} {w}) == braid* {n} {f w}
  f-braid-β = apd=cst-in E.f-braid-β

infixr 50 _++_

_++_ : ∀ {m} → CList m → CList m → CList m
_++_ {m} = CListRec.f (λ w → w) (λ n f w → n :: f w) (λ= λ _ → cancel) (λ p → λ= λ _ → swap p) (λ= λ _ → braid)

instance
  clist-paths-prop : ∀ {m} → {w1 w2 : CList m} → is-prop (w1 == w2)
  clist-paths-prop = has-level-apply trunc _ _

++-unit-r : ∀ {m} (l : CList m) → l ++ nil == l
++-unit-r = CListElimProp.f idp (λ n {w} p → ap (n ::_) p) {{clist-paths-prop}}

++-assoc : ∀ {m} (l₁ l₂ l₃ : CList m) → (l₁ ++ l₂) ++ l₃ == l₁ ++ (l₂ ++ l₃)
++-assoc = CListElimProp.f (λ _ _ → idp) (λ n {w} f l₂ l₃ → ap (n ::_) (f l₂ l₃)) {{Π-level λ _ → Π-level λ _ → clist-paths-prop}}