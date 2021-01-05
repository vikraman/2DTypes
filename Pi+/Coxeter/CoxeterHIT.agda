{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.CoxeterHIT where

open import lib.Base
open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.PathOver
open import lib.types.Nat using (_+_; <-ap-S)
open import lib.types.Sigma
open import lib.PathGroupoid
open import lib.Funext
open import lib.types.Pi
open import lib.types.Fin

open import Pi+.Misc
open import Pi+.Coxeter.Arithmetic
open import Pi+.Coxeter.MCoxeter
open import Pi+.Coxeter.MCoxeterS
open import Pi+.Coxeter.Diamond
open import Pi+.Extra


module _ (m : ℕ) where
  
  infixr 35 _::_

  ⟦S_⟧ : ∀ {n} → Fin n → Fin (S n)
  ⟦S (k , lt) ⟧ = S k , <-ap-S lt
  
  ⟦_⟧ : ∀ {n} → Fin n → Fin (S n)
  ⟦_⟧ = Fin-S

  postulate
    CList : Type₀
    nil : CList
    _::_ : Fin (S m) → CList → CList

    cancel : {n : Fin (S m)} {w : CList} -> (n :: n :: w) == w
    swap : {n : Fin (S m)} {k : Fin (S m)} → (S (k .fst) < (n .fst)) → {w : CList} → (n :: k :: w) == (k :: n :: w)
    braid : {n : Fin m} {w : CList} → (⟦S n ⟧ :: ⟦ n ⟧ :: ⟦S n ⟧ :: w) == (⟦ n ⟧ :: ⟦S n ⟧ :: ⟦ n ⟧ :: w)

    instance trunc : is-set CList

  [_] : Fin (S m) → CList
  [ n ] = n :: nil

  module CListElim {i} {P : CList → Type i}
    (nil* : P nil)
    (_::*_ : (n : Fin (S m)) {w : CList} (w* : P w) → P (n :: w))
    (cancel* : {n : Fin (S m)} {w : CList} {w* : P w} → (n ::* (n ::* w*)) == w* [ P ↓ cancel ])
    (swap* : {n : Fin (S m)} {k : Fin (S m)} → (p : S (k .fst) < (n .fst)) → {w : CList} {w* : P w} → (n ::* (k ::* w*)) == (k ::* (n ::* w*)) [ P ↓ swap p ])
    (braid* : {n : Fin m} {w : CList} {w* : P w} → (⟦S n ⟧ ::* (⟦ n ⟧ ::* (⟦S n ⟧ ::* w*))) == (⟦ n ⟧ ::* (⟦S n ⟧ ::* (⟦ n ⟧ ::* w*))) [ P ↓ braid ])
    {{trunc* : {w : CList} → is-set (P w)}}
    where

    postulate
      f : (w : CList) → P w
      f-nil-β : f nil ↦ nil*
      {-# REWRITE f-nil-β #-}
      f-::-β : {n : Fin (S m)} {w : CList} → f (n :: w) ↦ (n ::* (f w))
      {-# REWRITE f-::-β #-}

    postulate
      f-cancel-β : {n : Fin (S m)} {w : CList} → apd f (cancel {n} {w}) == cancel* {n} {w}
      f-swap-β : {n : Fin (S m)} {k : Fin (S m)} {w : CList} → (p : S (k .fst) < (n .fst)) → apd f (swap {n} {k} p {w}) == swap* p {w}
      f-braid-β : {n : Fin m} {w : CList} → apd f (braid {n} {w}) == braid* {n} {w}

  module CListElimProp {i} {P : CList → Type i}
    (nil* : P nil)
    (_::*_ : (n : Fin (S m)) {w : CList} (w* : P w) → P (n :: w))
    {{trunc* : {w : CList} → is-prop (P w)}}
    where
    private module E = CListElim {P = P} nil* _::*_ prop-has-all-paths-↓ (λ p → prop-has-all-paths-↓) prop-has-all-paths-↓
    f : (w : CList) → P w
    f = E.f {{raise-level -1 trunc*}}

  module CListRec {i} {P : Type i}
    (nil* : P)
    (_::*_ : (n : Fin (S m)) (w* : P) → P)
    (cancel* : {n : Fin (S m)} {w* : P} → (n ::* (n ::* w*)) == w*)
    (swap* : {n : Fin (S m)} {k : Fin (S m)} → (p : S (k .fst) < (n .fst)) → {w* : P} → (n ::* (k ::* w*)) == (k ::* (n ::* w*)))
    (braid* : {n : Fin m} {w* : P} → (⟦S n ⟧ ::* (⟦ n ⟧ ::* (⟦S n ⟧ ::* w*))) == (⟦ n ⟧ ::* (⟦S n ⟧ ::* (⟦ n ⟧ ::* w*))))
    {{trunc* : is-set P}}
    where

    private module E = CListElim {P = λ _ → P} nil* (λ n p → n ::* p) (↓-cst-in cancel*) (λ p → ↓-cst-in (swap* p)) (↓-cst-in braid*)

    f : CList → P
    f = E.f

    f-cancel-β : {n : Fin (S m)} {w : CList} → ap f (cancel {n} {w}) == cancel* {n} {f w}
    f-cancel-β = apd=cst-in E.f-cancel-β

    f-swap-β : {n : Fin (S m)} {k : Fin (S m)} → (p : S (k .fst) < (n .fst)) {w : CList} → ap f (swap {n} {k} p {w}) == swap* p {f w}
    f-swap-β p = apd=cst-in (E.f-swap-β p)

    f-braid-β : {n : Fin m} {w : CList} → ap f (braid {n} {w}) == braid* {n} {f w}
    f-braid-β = apd=cst-in E.f-braid-β

-- infixr 50 _++_

-- _++_ : ∀ {m} → CList m → CList m → CList m
-- _++_ {m} = CListRec.f (λ w → w) (λ n f w → n :: f w) (λ= λ _ → cancel) (λ p → λ= λ _ → swap p) (λ= λ _ → braid)

-- instance
--   clist-paths-prop : ∀ {m} → {w1 w2 : CList m} → is-prop (w1 == w2)
--   clist-paths-prop = has-level-apply trunc _ _

-- ++-unit-r : l → l ++ nil == l
-- ++-unit-r = CListElimProp.f idp (λ n {w} p → ap (n ::_) p) {{clist-paths-prop}}

-- ++-assoc : ∀ l₁ l₂ l₃ → (l₁ ++ l₂) ++ l₃ == l₁ ++ (l₂ ++ l₃)
-- ++-assoc = CListElimProp.f (λ _ _ → idp) (λ n {w} f l₂ l₃ → ap (n ::_) (f l₂ l₃)) {{Π-level λ _ → Π-level λ _ → clist-paths-prop}}
