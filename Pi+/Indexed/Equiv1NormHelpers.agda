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
open import Pi+.Indexed.Equiv1Hat
open import Pi+.Indexed.Level0Hat
open import Pi+.Indexed.Level0

open import Pi+.Misc
open import Pi+.Extra
open import Pi+.UFin.Base
open import Pi+.Common.FinHelpers
open import Pi+.Coxeter.Coxeter
open import Pi+.Coxeter.Sn

private
  variable
    n m o : ℕ

postulate
    ℕ-S-is-inj-rewrite : {n : ℕ} -> (ℕ-S-is-inj n n idp) ↦ idp -- path in ℕ
    {-# REWRITE ℕ-S-is-inj-rewrite #-}

list2normI : (n == m) → List (Fin n) → S n ⟷₁^ S m
list2normI idp l = list2norm^ l

piRespectsCoxI : (p : n == m) → (l₁ l₂ : List (Fin n)) → (l₁ ≈ l₂) →
                (list2normI {n = n} {m = m} p l₁) ⟷₂^ (list2normI {n = n} {m = m} p l₂)
piRespectsCoxI idp _ _ c = piRespectsCox^ _ _ _ c

norm2list : (S n) ⟷₁^ (S m) → List (Fin n)
norm2list swap₊^ = fzero :: nil
norm2list id⟷₁^ = nil
norm2list (c ◎^ c₁) with (⟷₁^-eq-size c) | (⟷₁^-eq-size c₁)
... | idp | idp = norm2list c ++ norm2list c₁
norm2list {O} (⊕^ c) = nil
norm2list {S n} (⊕^ c) with (⟷₁^-eq-size c)
... | idp = map S⟨_⟩ (norm2list c)

norm2norm : (c : S n ⟷₁^ S m) →
    (list2normI (ℕ-S-is-inj _ _ (⟷₁^-eq-size c)) (norm2list c)) ⟷₂^ c
norm2norm (swap₊^ {n = n}) 
    rewrite (ℕ-p (+-assoc 1 1 n))
    rewrite (ℕ-p (+-unit-r 1)) 
    rewrite (ℕ-p (+-assoc 1 0 1)) = 
    -- Code duplication with Eval1Hat
        _ ⟷₂^⟨ idr◎l^ ⟩
        _ ⟷₂^⟨ idl◎l^ ⟩
        _ ⟷₂^⟨ idr◎l^ ⟩
        _ ⟷₂^⟨ ⊕⊕id⟷₁⟷₂^ ⊡^ ((id⟷₂^ ⊡^ ⊕⊕id⟷₁⟷₂^) ⊡^ (⊕⊕id⟷₁⟷₂^ ⊡^ ⊕⊕id⟷₁⟷₂^)) ⟩
        _ ⟷₂^⟨ idl◎l^ ⟩
        _ ⟷₂^⟨ idr◎l^ ⊡^ idl◎l^ ⟩
        _ ⟷₂^⟨ idr◎l^ ⟩
        swap₊^ ⟷₂^∎
norm2norm id⟷₁^ = id⟷₂^
norm2norm (c₁ ◎^ c₂) with (⟷₁^-eq-size c₂) | (⟷₁^-eq-size c₁)
... | idp | idp = 
  let r₁ = norm2norm c₁
      r₂ = norm2norm c₂
  in  trans⟷₂^ TODO (r₁ ⊡^ r₂)
norm2norm {O} (⊕^ c) with (⟷₁^-eq-size c)
... | idp = !⟷₂^ (trans⟷₂^ (resp⊕⟷₂ (c₊⟷₂id⟷₁ c)) ⊕id⟷₁⟷₂^)
norm2norm {S n} (⊕^ c) with (⟷₁^-eq-size c)
... | idp = 
  let rec = norm2norm c
  in  TODO

list2list : {n : ℕ} → (p : List (Fin n)) → norm2list (list2normI idp p) == p
list2list nil = idp
list2list {S n} ((O , p0) :: p) 
    rewrite (ℕ-p (+-assoc 1 1 n))
    rewrite (ℕ-p (+-unit-r 1)) 
    rewrite (ℕ-p (+-assoc 1 0 1)) = 
      let rec = list2list p 
      in  TODO
list2list {S n} ((S k , pk) :: p) = TODO
