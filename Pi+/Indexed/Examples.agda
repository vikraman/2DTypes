{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Base
-- open import lib.NType
-- open import lib.PathFunctor
-- open import lib.PathGroupoid
import lib.types.Nat as N

open import Pi+.Misc
open import Pi+.Extra

module Pi+.Indexed.Examples where

open import Pi+.Indexed.Syntax as Pi+
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.Indexed.SyntaxHatHelpers as Pi^
open import Pi+.Indexed.SyntaxFull as Pi
open import Pi+.Indexed.Translation

private
  variable
    m n o p q r : ℕ

𝟚 : Pi.U
𝟚 = I + I

controlled : {t : Pi.U} → (c : t Pi.⟷₁ t) → (𝟚 Pi.× t Pi.⟷₁ 𝟚 Pi.× t)
controlled c = Pi.dist ◎ (id⟷₁ ⊕ (id⟷₁ ⊗ c)) ◎ factor

not : 𝟚 Pi.⟷₁ 𝟚
not = swap₊

not^ : 2 Pi^.⟷₁^ 2
not^ = eval₁ not

cnot : 𝟚 Pi.× 𝟚 Pi.⟷₁ 𝟚 Pi.× 𝟚
cnot = controlled not

cnot^ : 4 ⟷₁^ 4
cnot^ = eval₁ cnot

toffoli : 𝟚 Pi.× (𝟚 Pi.× 𝟚) Pi.⟷₁ 𝟚 Pi.× (𝟚 Pi.× 𝟚)
toffoli = controlled cnot

toffoli^ : 8 ⟷₁^ 8
toffoli^ = eval₁ toffoli
