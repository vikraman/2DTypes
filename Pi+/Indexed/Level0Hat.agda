{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.Indexed.Level0Hat where

-- open import lib.Base
-- open import lib.PathGroupoid
-- open import lib.types.Nat renaming (_+_ to _+ℕ_)
-- open import lib.types.Sigma
-- open import lib.types.Fin
-- open import lib.types.List
-- open import lib.NType

-- open import Pi+.Indexed.Syntax as Pi
-- open import Pi+.Indexed.SyntaxHat as Pi^
-- open import Pi+.Indexed.Level0

-- open import Pi+.Indexed.Equiv1Hat
-- open import Pi+.Indexed.Equiv2Hat

-- open import Pi+.Misc
-- open import Pi+.Extra

-- open import Pi+.Common.FinHelpers
-- open import Pi+.Coxeter.Coxeter
-- open import Pi+.Coxeter.Sn

-- -----------------------------------------------------------------------------
-- -- Canonical representation of sum types as "lists" I + (I + (I + ... O))

-- private
--   variable
--     n m p : ℕ

-- -----------------------------------------------------------------------------
-- -- Mapping betweem pi combinators over non-zero types to and from the
-- -- Coxeter representation

-- -- Mapping each transposition index to a combinator and
-- -- some properties
