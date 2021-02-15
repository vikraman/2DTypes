{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.Indexed.Equiv1NormHelpers where

open import lib.Base
open import lib.PathGroupoid
open import lib.types.Nat renaming (_+_ to _+ℕ_)
open import lib.types.Sigma
open import lib.types.Fin
open import lib.types.List
open import lib.NType

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.Indexed.Equiv0Norm
open import Pi+.Indexed.Level0Hat

open import Pi+.Misc
open import Pi+.Extra
open import Pi+.UFin.Base
open import Pi+.Common.FinHelpers
open import Pi+.Coxeter.Coxeter
open import Pi+.Coxeter.Sn

private
  variable
    n m o : ℕ

list2normI : {t₁ : U^ (S n)} {t₂ : U^ (S m)} → (n == m) → List (Fin n) → t₁ ⟷₁^ t₂
list2normI {n} {t₁ = t₁} {t₂ = t₂} idp l rewrite (U^-is-Singleton t₁ (i^ (S n))) rewrite (U^-is-Singleton t₂ (i^ (S n))) = list2norm^ l

piRespectsCoxI : {t₁ : U^ (S n)} {t₂ : U^ (S m)} → (p : n == m) → (l₁ l₂ : List (Fin n)) → (l₁ ≈ l₂) →
                (list2normI {t₁ = t₁} {t₂ = t₂} p l₁) ⟷₂^ (list2normI {t₁ = t₁} {t₂ = t₂} p l₂)
piRespectsCoxI {n} {t₁ = t₁} {t₂ = t₂} idp _ _ c rewrite (U^-is-Singleton t₁ (i^ (S n))) rewrite (U^-is-Singleton t₂ (i^ (S n))) = piRespectsCox^ _ _ _ c

norm2list : {t₁ : U^ (S n)} {t₂ : U^ m} → t₁ ⟷₁^ t₂ → List (Fin n)
norm2list swap₊^ = fzero :: nil
norm2list id⟷₁^ = nil
norm2list (_◎^_ {.(S _)} {_} {O} c₁ c₂) = nil
norm2list (_◎^_ {.(S _)} {_} {S o} c₁ c₂) = (norm2list c₁) ++ transport (λ e -> List (Fin e)) (ℕ-S-is-inj _ _ (! (⟷₁^-eq-size c₁))) (norm2list c₂)
norm2list {n = O} (⊕^ c) = nil
norm2list {n = S n} (⊕^ c) = map S⟨_⟩ (norm2list c)

-- -- Back and forth identities

norm2norm : {t₁ : U^ (S n)} {t₂ : U^ (S m)} → (c : t₁ ⟷₁^ t₂) →
    (list2normI {t₁ = t₁} {t₂ = t₂} (ℕ-S-is-inj _ _ (⟷₁^-eq-size c)) (norm2list c)) ⟷₂^ c
norm2norm (swap₊^ {t = t}) = TODO
norm2norm id⟷₁^ = TODO
norm2norm (_◎^_ {.(S _)} {_} {O} c₁ c₂) = TODO -- impossible
norm2norm (_◎^_ {.(S _)} {_} {S o} c₁ c₂) =
  let r1 = norm2norm c₁ 
      r2 = norm2norm c₂
  in  TODO
norm2norm {n = O} (⊕^ c) = TODO -- zero case
norm2norm {n = S n} (⊕^ c) = TODO
  -- let rec = norm2norm c
  -- in  TODO

list2list : {n : ℕ} → (p : List (Fin n)) → 
  norm2list {t₁ = quoteNorm₀ (pFin _)} {t₂ = quoteNorm₀ (pFin _)} (list2normI {t₁ = quoteNorm₀ (pFin _)} {t₂ = quoteNorm₀ (pFin _)} idp p) == p
list2list nil = TODO
list2list {S n} ((O , fp) :: ns) = TODO
  -- let rec = list2list ns
  --     n2n = norm2list (list2norm ns)
  --     tt = transport (λ e → List (Fin e)) (ℕ-S-is-inj (S n) (S n) idp) n2n == transport (λ e → List (Fin e)) idp n2n
  --     tt = ap (λ x → transport (λ e → List (Fin e)) x n2n) ℕ-S-is-inj-idp
  -- in  List=-out ((Fin= _ _ idp (O<S n) fp) , (tt ∙ rec))
list2list {S n} ((S x , fp) :: ns) = TODO

-- -----------------------------------------------------------------------------

