{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Misc where

open import HoTT

transport2 : ∀ {i j k} {A : Type i} {B : Type j} (C : A → B → Type k) {x1 x2 : A} {y1 y2 : B} (p : x1 == x2) (q : y1 == y2)
  → (C x1 y1 → C x2 y2)
transport2 C {x1} {x2} {y1} {y2} p q t = t''
    where
        t' : C x1 y2
        t' = transport (C x1) q t

        t'' : C x2 y2
        t'' = transport (λ x -> C x y2) p t'

transport2-equiv : ∀ {i j k} {A : Type i} {B : Type j} (C : A → B → Type k) {x1 x2 : A} {y1 y2 : B} (p : x1 == x2) (q : y1 == y2)
  → (C x1 y1 ≃ C x2 y2)
transport2-equiv C idp idp = ide _