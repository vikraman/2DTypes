{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

open import HoTT hiding (_<_ ; ltS ; ltSR ; _+_ ; _×_)
import lib.types.Nat as N
import lib.types.Sigma as S

open import Pi.UFin.BAut
open import Pi.Common.Misc
open import Pi.Common.Extra

-- open import Pi.Syntax.Pi+.Indexed as Pi+
open import Pi.Syntax.Pi^ as Pi^
open import Pi.Syntax.Pi^Helpers as Pi^
open import Pi.Syntax.Pi as Pi
-- open import Pi.Equiv.Translation2
-- import Pi.Equiv.Equiv1 as Pi+
-- import Pi.Equiv.Equiv0Hat as Pi^
-- import Pi.Equiv.Equiv1Hat as Pi^
-- import Pi.Equiv.Equiv0Norm as Pi^
-- import Pi.Equiv.Equiv1Norm as Pi^
-- open import Pi.UFin.UFin
-- open import Pi.UFin.Monoidal
-- open import Pi.Common.FinHelpers
-- open import Pi.Lehmer.FinExcept

module Pi.Examples.EH where

open import Pi.Examples.Base

module A (p q : I ⟷₁ I) where

  c1 : I ⟷₁ I × I
  c1 = uniti⋆l

  c2 : (p ⊗ p) ⟷₂ (p ⊗ id⟷₁ {I})
  c2 = {!!}

  c9 : q ⟷₂ q ◎ id⟷₁
  c9 = idr◎r

  α : p ◎ q ⟷₂ q ◎ p
  α = trans⟷₂ ({!!} ⊡ id⟷₂)
      {!!}

++^-r-0 : (p : 0 ⟷₁^ 0) → p ⟷₂^ ++^-r p
++^-r-0 id⟷₁^ = id⟷₂^
++^-r-0 (p ◎^ q) with ⟷₁^-eq-size p | ⟷₁^-eq-size q
... | idp | idp = ++^-r-0 p ⊡^ ++^-r-0 q

postulate
  exch : (p q : 0 ⟷₁^ 0)
       → ++^-r {o = 0} p ◎^ ++^-l {o = 0} q ⟷₂^ ++^-⊕ (p ◎^ id⟷₁^) (id⟷₁^ ◎^ q)
  exch' : (p q : 0 ⟷₁^ 0)
       → ++^-l {o = 0} p ◎^ ++^-r {o = 0} q ⟷₂^ ++^-⊕ (q ◎^ id⟷₁^) (id⟷₁^ ◎^ p)

module B (p q : 0 ⟷₁^ 0) where

  eh : (p ◎^ q) ⟷₂^ (q ◎^ p)
  eh = let r = c₊⟷₂id⟷₁^ p
           s = c₊⟷₂id⟷₁^ q
       in (r ⊡^ s) ■^ (!⟷₂^ s ⊡^ !⟷₂^ r)

  α : (p ◎^ q) ⟷₂^ (q ◎^ p)
  α = p ◎^ q
    ⟷₂^⟨ ++^-r-0 p ⊡^ id⟷₂^ ⟩
      ++^-r {o = 0} p ◎^ q
    ⟷₂^⟨ id⟷₂^ ⟩
      ++^-r {o = 0} p ◎^ ++^-l {o = 0} q
    ⟷₂^⟨ exch p q ⟩
      ++^-⊕ (p ◎^ id⟷₁^) (id⟷₁^ ◎^ q)
    ⟷₂^⟨ ++^-⊕-◎ idr◎l^ idl◎l^ ⟩
      ++^-⊕ p q
    ⟷₂^⟨ {!!} ⟩
      ++^-l {o = 0} p ◎^ q
    ⟷₂^⟨ {!!} ⟩
      ++^-l {o = 0} p ◎^ (++^-r {o = 0} q)
    ⟷₂^⟨ !⟷₂^ {!!} ⟩
      ++^-⊕ (id⟷₁^ ◎^ p) (q ◎^ id⟷₁^)
    ⟷₂^⟨ !⟷₂^ {!!} ⟩
      ++^-l {o = 0} q ◎^ ++^-r {o = 0} p
    ⟷₂^⟨ id⟷₂^ ⟩
      q ◎^ ++^-r {o = 0} p
    ⟷₂^⟨ id⟷₂^ ⊡^ !⟷₂^ (++^-r-0 p) ⟩
      q ◎^ p
    ⟷₂^∎

11-id : (p : 1 ⟷₁^ 1) → p ⟷₂^ id⟷₁^
11-id id⟷₁^ = id⟷₂^
11-id (p ◎^ q) with ⟷₁^-eq-size p | ⟷₁^-eq-size q
... | idp | idp = (11-id p ⊡^ 11-id q) ■^ idl◎l^
11-id (⊕^ p) = resp⊕⟷₂ (c₊⟷₂id⟷₁^ p) ■^ ⊕id⟷₁⟷₂^
