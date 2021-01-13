{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Parametrized.ListFinLListEquiv where

open import lib.Base
open import lib.types.Nat using (_+_; O<S; <-ap-S; <-has-all-paths) renaming (_<_ to _<N_)
open import lib.types.Sigma
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.Equivalence
open import lib.types.List

open import Pi+.Extra
open import Pi+.Coxeter.Common.Arithmetic
open import Pi+.Coxeter.Common.ListN
open import Pi+.Coxeter.Common.LList
open import Pi+.Coxeter.Parametrized.Coxeter
open import Pi+.Coxeter.Parametrized.InequalityEquiv

module _ {n : ℕ} where
  
  List≃LList : List (Fin n) ≃ (LList n)
  List≃LList = equiv f g TODO TODO
    where
      f : List (Fin n) -> (LList n)
      f nil = nil , nil
      f (x :: l) = 
        let rec-l , rec-p = f l
        in  ((x . fst) ∷ rec-l) , ((x .fst) :⟨ –> <N≃< (x .snd) ⟩: rec-p)

      g : (LList n) -> List (Fin n)
      g (nil , nil) = nil
      g ((x ∷ fst) , (.x :⟨ px ⟩: snd)) = (x , (<– <N≃< px)) :: g (fst , snd)
