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

module Pi.Examples.Copy where

open import Pi.Examples.Base
open import Pi.Examples.Toffoli

-- copy(𝔽,b₁,…,bₙ) = (b₁,b₁,…,bₙ)
copy : ∀ n → 𝟚 Pi.× 𝔹 n Pi.⟷₁ 𝟚 Pi.× 𝔹 n
copy O = id⟷₁
copy (S O) = swap⋆ ◎ cnot ◎ swap⋆
copy (S (S n)) = assocl⋆ ◎ (copy (S O) ⊗ id⟷₁) ◎ assocr⋆

copy^ : ∀ n → _
copy^ = eval₁ ∘ copy

copy+ : ∀ n → _
copy+ = Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp ∘ Pi^.evalNorm₁ ∘ copy^

open import Pi.Examples.Interp

test-interp-copy1 = interp-elems (copy 1)
test-interp-copy1+ = interp+-elems (Pi^.quote^₁ (eval₁ (copy 1)))
test-interp-copy1^ = interp+-elems (copy+ 1)
test-encode-interp-copy1 = map encode-interp-elems test-interp-copy1

test-interp-copy2 = interp-elems (copy 2)
test-interp-copy2+ = interp+-elems (Pi^.quote^₁ (eval₁ (copy 2)))
test-interp-copy2^ = interp+-elems (copy+ 2)
test-encode-interp-copy2 = map encode-interp-elems test-interp-copy2
