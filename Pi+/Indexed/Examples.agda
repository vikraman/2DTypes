{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

open import HoTT hiding (_<_ ; ltS ; ltSR ; _+_ ; _×_)
import lib.types.Nat as N
import lib.types.Sigma as S

open import Pi+.UFin.BAut
open import Pi+.Misc
open import Pi+.Extra

open import Pi+.Indexed.Syntax as Pi+
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.Indexed.SyntaxHatHelpers as Pi^
open import Pi+.Indexed.SyntaxFull as Pi
open import Pi+.Indexed.Translation2
import Pi+.Indexed.Equiv1 as Pi+
import Pi+.Indexed.Equiv0Hat as Pi^
import Pi+.Indexed.Equiv1Hat as Pi^
import Pi+.Indexed.Equiv0Norm as Pi^
import Pi+.Indexed.Equiv1Norm as Pi^
open import Pi+.UFin
open import Pi+.UFin.Monoidal
open import Pi+.Common.FinHelpers
open import Pi+.Lehmer.FinHelpers

module Pi+.Indexed.Examples where
