{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

module Pi.UFin.BAut where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.PathGroupoid
open import lib.PathOver
open import lib.Equivalence
open import lib.Equivalence2
open import lib.Univalence
open import lib.Funext
open import lib.types.Empty
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Truncation
open import lib.types.BAut
open import lib.types.LoopSpace

BAut-fst-level : ∀ {i} {n : ℕ₋₂} {T : Type i} {{φ : has-level n T}} → (X : BAut T) → has-level n (fst X)
BAut-fst-level {n = n} {{φ}} (X , ψ) = Trunc-elim (λ p → transport (has-level n) p φ) ψ

BAut= : ∀ {i} {T : Type i} (X Y : BAut T) → Type (lsucc i)
BAut= {T = T} = Subtype= (BAut-prop T)

BAut=-econv : ∀ {i} {T : Type i} (X Y : BAut T) → (BAut= X Y) ≃ (X == Y)
BAut=-econv {T = T} = Subtype=-econv (BAut-prop T)

instance
  BAut-level : ∀ {i} {n : ℕ₋₂} {T : Type i} {{φ : has-level n T}} → has-level (S n) (BAut T)
  BAut-level =
    has-level-in λ { X Y → equiv-preserves-level (BAut=-econv X Y)
                           {{universe-=-level (BAut-fst-level X) (BAut-fst-level Y)}} }

module _ {i} (T : Type i) where

  Aut : Type i
  Aut = T ≃ T

  pAut : Ptd i
  pAut = ⊙[ Aut , ide T ]

-- NOTE: We're defining it from scratch because we need this to compute, it
-- could be defined simply using ≃-level, but that uses ≃-contr which is marked
-- abstract.

instance
  Aut-level : ∀ {i} {T : Type i} {n : ℕ₋₂} {{_ : has-level n T}} → has-level n (Aut T)
  Aut-level {n = ⟨-2⟩} =
    has-level-in (ide _ , λ { (f , ϕ) → pair= (contr-has-all-paths (idf _) f) prop-has-all-paths-↓ })
  Aut-level {n = S n} =
    Σ-level (Π-level (λ _ → ⟨⟩)) λ _ → prop-has-level-S ⟨⟩

module _ {i} (T : Type i) where

  ⊙ΩBAut : Ptd (lsucc i)
  ⊙ΩBAut = ⊙Ω (pBAut T)

  ΩBAut : Type (lsucc i)
  ΩBAut = de⊙ ⊙ΩBAut

module _ {i} (T : Type i) where

  loop-equiv : ΩBAut T ≃ Aut T
  loop-equiv = equiv f g f-g g-f
    where f : ΩBAut T → Aut T
          f p = coe-equiv (fst= p)
          g : Aut T → ΩBAut T
          g e = pair= (ua e) prop-has-all-paths-↓
          f-g : (e : Aut T) → f (g e) == e
          f-g e = pair= (ap coe (fst=-β (ua e) prop-has-all-paths-↓) ∙ λ= (coe-β e)) prop-has-all-paths-↓
          g-f : (p : ΩBAut T) → g (f p) == p
          g-f p = ap (g ∘ f) (pair=-η p)
                ∙ ap g (pair= (ap coe (fst=-β (fst= p) (snd= p))) prop-has-all-paths-↓)
                ∙ ap (λ q → pair= q prop-has-all-paths-↓) (ua-η (fst= p))
                ∙ pair== idp (contr-has-all-paths
                             ⦃ equiv-preserves-level (to-transp-equiv _ (fst= p) ⁻¹)
                               ⦃ has-level-apply Trunc-level _ _ ⦄ ⦄
                             prop-has-all-paths-↓ (snd= p))
                ∙ ! (pair=-η p)

  ⊙loop-equiv : ⊙ΩBAut T ⊙≃ pAut T
  ⊙loop-equiv = ≃-to-⊙≃ loop-equiv idp

open import homotopy.FinSet
open import lib.types.Fin

pFinSet-exp : (n : ℕ) → Ptd (lsucc lzero)
de⊙ (pFinSet-exp n) = FinSet-exp
pt (pFinSet-exp n) = n , pt (pBAut (Fin n))

Fin-loop-equiv : (n : ℕ) → ΩBAut (Fin n) ≃ Aut (Fin n)
Fin-loop-equiv n = loop-equiv (Fin n)

pFin-loop-equiv : (n : ℕ) → ⊙ΩBAut (Fin n) ⊙≃ pAut (Fin n)
pFin-loop-equiv n = ⊙loop-equiv (Fin n)

instance
  Aut-FinO-level : is-contr (Aut (Fin O))
  Aut-FinO-level =
    inhab-prop-is-contr (ide _)
      {{Aut-level {{equiv-preserves-level (Fin-equiv-Empty ⁻¹)}}}}
