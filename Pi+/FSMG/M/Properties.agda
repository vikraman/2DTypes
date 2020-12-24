{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.FSMG.M.Properties where

open import lib.Base
open import lib.Equivalence
open import lib.NType
open import lib.types.Truncation

open import Pi+.Extra
open import Pi+.FSMG.M as M
open import Pi+.FSMG.SMG

module _ {i} {A : Type i} where

  instance
    M-SMGStructure : SMGStructure (M A)
    M-SMGStructure = TODO

  module _ {j} {N : Type j} {{_ : has-level 1 N}} {{GN : SMGStructure N}} where

    M-Universal : SMFunctor (M A) N ≃ (A → N)
    M-Universal = TODO
