{-# OPTIONS --without-K --exact-split #-}

open import lib.Base
open import lib.PathOver

module Pi+.FSMG.Paths where

_■_ : ∀ {i} {j}
    → {A : Type i} {P : A → Type j}
    → {x y z : A} {u : P x} {v : P y} {w : P z}
    → {p : x == y} {q : y == z}
    → u == v [ P ↓ p ] → v == w [ P ↓ q ] → u == w [ P ↓ (p ∙ q) ]
_■_ {p = idp} {idp} s t = s ∙ t

$ : ∀ {i} {j}
  → {A : Type i} {P : A → Type j}
  → {x y : A} {u : P x} {v : P y}
  → {f : A → A} (g : {x : A} → P x → P (f x))
  → {p : x == y}
  → u == v [ P ↓ p ] → g u == g v [ P ↓ ap f p ]
$ g {idp} s = ap g s
