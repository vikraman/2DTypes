{-# OPTIONS --without-K --exact-split --rewriting --allow-unsolved-metas #-}

open import lib.Base
open import lib.NType
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.types.Nat as N renaming (_+_ to _++_)

open import Pi+.Misc as N renaming (_*_ to _**_)
open import Pi+.Extra

module Pi+.Indexed.Translation2 where

open import Pi+.NonIndexed.Syntax as Pi+
open import Pi+.Indexed.SyntaxFull as Pi

private
  variable
    m n o p q r : ℕ

eval₀-aux : Pi.U → ℕ
eval₀-aux O = O
eval₀-aux I = S O
eval₀-aux (t₁ + t₂) = eval₀-aux t₁ N.+ eval₀-aux t₂
eval₀-aux (t₁ × t₂) = eval₀-aux t₁ N.* eval₀-aux t₂

eval₀ : Pi.U → Pi+.U
eval₀ O = O
eval₀ I = I
eval₀ (t₁ + t₂) = eval₀ t₁ + eval₀ t₂
eval₀ (t₁ × t₂) = {!!}
