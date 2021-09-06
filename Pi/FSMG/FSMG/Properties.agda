{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.FSMG.FSMG.Properties where

open import lib.Base
open import lib.Equivalence
open import lib.Equivalence2
open import lib.Funext
open import lib.PathGroupoid
open import lib.NType
open import lib.types.Truncation

open import Pi.Extra
open import Pi.FSMG.FSMG as F
open import Pi.FSMG.SMG

module _ {i} {A : Type i} where

  instance
    FSMG-SMGStructure : SMGStructure (FSMG A)
    SMGStructure.I FSMG-SMGStructure = F.I
    SMGStructure._⊗_ FSMG-SMGStructure = F._⊗_
    SMGStructure.α FSMG-SMGStructure = F.α
    SMGStructure.Λ FSMG-SMGStructure = F.Λ
    SMGStructure.ρ FSMG-SMGStructure = F.ρ
    SMGStructure.β FSMG-SMGStructure = F.β
    SMGStructure.⬠ FSMG-SMGStructure = F.⬠
    SMGStructure.▽ FSMG-SMGStructure = F.▽
    SMGStructure.⬡ FSMG-SMGStructure = F.⬡
    SMGStructure.β² FSMG-SMGStructure = F.β²

  module _ {j} {M : Type j} {{_ : has-level 1 M}} {{GM : SMGStructure M}} where
    private
      module M = SMGStructure GM

    module _ (f : A → M) where
      private
        module R = FSMGRec {P = M} f M.I M._⊗_ M.α M.Λ M.ρ M.β M.⬠ M.▽ M.⬡ M.β² ⟨⟩

      private
        f♯ : FSMG A → M
        f♯ = R.f

      _♯ : SMFunctor (FSMG A) M
      SMFunctor.f _♯ = f♯
      SMFunctor.f-I _♯ = idp
      SMFunctor.f-⊗ _♯ = idp
      SMFunctor.f-α _♯ = ∙-unit-r _ ∙ R.f-α-β
      SMFunctor.f-Λ _♯ = R.f-Λ-β
      SMFunctor.f-ρ _♯ = R.f-ρ-β
      SMFunctor.f-β _♯ = ∙-unit-r _ ∙ R.f-β-β

    module _ (f : A → M) (H : SMFunctor (FSMG A) M) (H-η : (H .SMFunctor.f) ∘ η == f) where
      f♯-uniq : (f ♯) == H
      f♯-uniq = sm-functor= (f ♯) H (! (λ= p)) TODO TODO
        where p : (X : FSMG A) → SMFunctor.f H X == SMFunctor.f (f ♯) X
              p = FSMGElimSet.f {{TODO}} (app= H-η) (SMFunctor.f-I H) (λ {X} {Y} X* Y* → SMFunctor.f-⊗ H {X} {Y} ∙ ap (M._⊗ _) X* ∙ ap (_ M.⊗_) Y*) TODO TODO TODO TODO

    FSMG-Universal : SMFunctor (FSMG A) M ≃ (A → M)
    FSMG-Universal = equiv (λ F → F .SMFunctor.f ∘ η) (λ f → f ♯) (λ _ → idp) h
      where h : (F : SMFunctor (FSMG A) M) → ((F .SMFunctor.f ∘ η) ♯) == F
            h F = sm-functor= ((S.f ∘ η) ♯) F TODO TODO TODO
              where module S = SMFunctor F
