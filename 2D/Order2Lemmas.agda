{-# OPTIONS --without-K #-}

module 2D.Order2Lemmas where

open import Data.Nat using (suc)
open import Data.Integer
  using (ℤ; +_; -[1+_])

open import Data.Nat.DivMod using (_mod_)
open import Data.Fin using (Fin; toℕ)

open import 2D.Types
open import 2D.Iter
open import 2D.Order

------------------------------------------------------------------------------
-- Lemmas useful for foldSwap/unfoldSwap

mod2 : (n : ℤ) → Fin 2
mod2 (+ n) = n mod 2
mod2 -[1+ n ] = (suc n) mod 2

--------------------------------------------------


