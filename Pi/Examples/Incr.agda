{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

open import HoTT hiding (_<_ ; ltS ; ltSR ; _+_ ; _×_)
import lib.types.Nat as N
import lib.types.Sigma as S

open import Pi.UFin.BAut
open import Pi.Common.Misc
open import Pi.Common.Extra

open import Pi.Syntax.Pi+.Indexed as Pi+
open import Pi.Syntax.Pi^ as Pi^
open import Pi.Syntax.Pi^Helpers as Pi^
open import Pi.Syntax.Pi as Pi
open import Pi.Equiv.Translation2
import Pi.Equiv.Equiv1 as Pi+
import Pi.Equiv.Equiv0Hat as Pi^
import Pi.Equiv.Equiv1Hat as Pi^
import Pi.Equiv.Equiv0Norm as Pi^
import Pi.Equiv.Equiv1Norm as Pi^
open import Pi.UFin.UFin
open import Pi.UFin.Monoidal
open import Pi.Common.FinHelpers
open import Pi.Lehmer.FinExcept

module Pi.Examples.Incr where

open import Pi.Examples.Base
open import Pi.Examples.Toffoli
open import Pi.Examples.Reset

fst2last : ∀ n → 𝔹 n Pi.⟷₁ 𝔹 n
fst2last O = id⟷₁
fst2last (S O) = id⟷₁
fst2last (S (S O)) = swap⋆
fst2last (S (S (S n))) = rearrange 𝟚 𝟚 (𝔹 (S n)) ◎ (id⟷₁ ⊗ fst2last (S (S n)))

incr : ∀ n → 𝔹 n Pi.⟷₁ 𝔹 n
incr O = id⟷₁
incr (S O) = swap₊
incr (S (S n)) = (id⟷₁ ⊗ incr (S n)) ◎ fst2last (S (S n)) ◎ toffoli (S (S n)) ◎ Pi.!⟷₁ (fst2last (S (S n)))

incr^ : ∀ n → _
incr^ = eval₁ ∘ incr

incr+ : ∀ n → _
incr+ = Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp ∘ Pi^.evalNorm₁ ∘ incr^

incr+test : Fin 4 → Fin 4
incr+test = –> (Pi+.eval₁ (incr+ 2))

incr+test-0 : incr+test 0 == 1
incr+test-0 = fin= idp

incr+test-1 : incr+test 1 == 2
incr+test-1 = fin= idp

incr+test-2 : incr+test 2 == 3
incr+test-2 = fin= idp

incr+test-3 : incr+test 3 == 0
incr+test-3 = fin= idp

open import Pi.Examples.Interp

test-interp-incr2 = interp-elems (incr 2)
test-interp-incr2+ = interp+-elems (Pi^.quote^₁ (eval₁ (incr 2)))
test-interp-incr2^ = interp+-elems (incr+ 2)
test-encode-interp-incr2 = map encode-interp-elems test-interp-incr2
