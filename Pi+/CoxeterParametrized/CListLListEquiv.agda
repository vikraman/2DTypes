{-# OPTIONS --without-K --rewriting #-}

module Pi+.CoxeterParametrized.CListLListEquiv where

open import lib.Base
open import lib.types.Nat using (_+_; O<S; <-ap-S; <-has-all-paths) renaming (_<_ to _<N_)
open import lib.types.Sigma
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.Equivalence

open import Pi+.Extra
open import Pi+.CoxeterCommon.Arithmetic
open import Pi+.CoxeterCommon.Lists
open import Pi+.CoxeterCommon.LList
open import Pi+.CoxeterParametrized.Coxeter
open import Pi+.CoxeterParametrized.InequalityEquiv

module _ {n : ℕ} where
  
  CList≃LList : CList n ≃ LList (S n)
  CList≃LList = equiv f g TODO TODO
    where
      f : (CList n) -> (LList (S n))
      f [] = nil , nil
      f (x ∷ l) = 
        let rec-l , rec-p = f l
        in  ((x . fst) :: rec-l) , ((x .fst) :⟨ –> <N≃< (x .snd) ⟩: rec-p)

      g : (LList (S n)) -> (CList n)
      g (nil , nil) = []
      g ((x :: fst) , (.x :⟨ px ⟩: snd)) = x , (<– <N≃< px) ∷ g (fst , snd)
