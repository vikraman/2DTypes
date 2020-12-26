{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.FSMG.FSMG.Properties where

open import lib.Base
open import lib.Equivalence
open import lib.NType
open import lib.types.Truncation

open import Pi+.Extra
open import Pi+.FSMG.FSMG as F
open import Pi+.FSMG.SMG

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

    FSMG-Universal : SMFunctor (FSMG A) M ≃ (A → M)
    FSMG-Universal = TODO
