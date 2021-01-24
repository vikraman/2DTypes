{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.FSMG.BAut where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.types.Sigma
open import lib.types.Truncation
open import lib.types.BAut

BAut-fst-level : ∀ {i} {n : ℕ₋₂} {T : Type i} {{φ : has-level n T}} → (X : BAut T) → has-level n (fst X)
BAut-fst-level {n = n} {{φ}} (X , ψ) = Trunc-elim (λ p → transport (has-level n) p φ) ψ

BAut= : ∀ {i} {T : Type i} (X Y : BAut T) → Type (lsucc i)
BAut= {T = T} = Subtype= (BAut-prop T)

BAut=-econv : ∀ {i} {T : Type i} (X Y : BAut T) → (BAut= X Y) ≃ (X == Y)
BAut=-econv {T = T} = Subtype=-econv (BAut-prop T)

instance
  BAut-level : ∀ {i} {n : ℕ₋₂} {T : Type i} {{φ : has-level n T}} → has-level (S n) (BAut T)
  BAut-level =
    has-level-in λ { X Y → equiv-preserves-level (BAut=-econv X Y)
                           {{universe-=-level (BAut-fst-level X) (BAut-fst-level Y)}} }
