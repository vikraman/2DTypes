{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.FSMG.UFin where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.Univalence
open import lib.types.Sigma
open import lib.types.Truncation
open import lib.types.BAut
open import lib.types.Nat
open import lib.types.Fin
open import lib.types.Pi
open import lib.types.Coproduct
open import homotopy.FinSet public

UFin : ∀ {i} → Type i → Type (lmax (lsucc lzero) i)
UFin A = Σ FinSet λ X → X .fst → A

open import Pi+.FSMG.SMG
open import Pi+.UFin.BAut

open import Pi+.Extra

instance
  BAut-Fin-level : {n : ℕ} → has-level 1 (BAut (Fin n))
  BAut-Fin-level = BAut-level {{Fin-is-set}}

  FinSet-exp-level : has-level 1 FinSet-exp
  FinSet-exp-level = Σ-level ⟨⟩ λ n → BAut-Fin-level

  FinSet-level : has-level 1 FinSet
  FinSet-level = equiv-preserves-level FinSet-econv {{FinSet-exp-level}}

FinSet-fst-level : (X : FinSet) → is-set (X .fst)
FinSet-fst-level (X , ϕ) = Trunc-elim (λ p → transport is-set (p .snd) Fin-is-set) ϕ

module _ {i} (A : Type i) {{_ : has-level 1 A}} where

  instance
    UFin-level : has-level 1 (UFin A)
    UFin-level = Σ-level FinSet-level λ X → ⟨⟩

  I : UFin A
  I = FinFS 0 , ⊥-elim ∘ –> Fin-equiv-Empty

  Fin+ : (m n : ℕ) → Fin (m + n) ≃ Fin m ⊔ Fin n
  Fin+ O n = TODO
  Fin+ (S m) n = TODO

  _∪_ : FinSet → FinSet → FinSet
  (X , ϕ) ∪ (Y , ψ) = X ⊔ Y , TODO

  _⊗_ : UFin A → UFin A → UFin A
  (X , F) ⊗ (Y , G) = (X ∪ Y) , TODO

  UFin-SMGStructure : SMGStructure (UFin A) {{UFin-level}}
  SMGStructure.I UFin-SMGStructure = I
  SMGStructure._⊗_ UFin-SMGStructure X Y = X ⊗ Y
  SMGStructure.α UFin-SMGStructure = TODO
  SMGStructure.Λ UFin-SMGStructure = TODO
  SMGStructure.ρ UFin-SMGStructure = TODO
  SMGStructure.β UFin-SMGStructure = TODO
  SMGStructure.⬠ UFin-SMGStructure = TODO
  SMGStructure.▽ UFin-SMGStructure = TODO
  SMGStructure.⬡ UFin-SMGStructure = TODO
  SMGStructure.β² UFin-SMGStructure = TODO
