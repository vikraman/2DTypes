{-# OPTIONS --without-K #-}

module 2D.ProgMorphisms where

open import Data.Product

open import 2D.Types
open import 2D.Sing
open import 2D.Iter
open import 2D.Power
open import 2D.Val

----------------------------------------------------------------------------
-- Note:  we don't need 'generic equivalences-of-equivalences' !
-- the operational semantics doesn't need them, and the denotational
-- semantics only needs each individual case

