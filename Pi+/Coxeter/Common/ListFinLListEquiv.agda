{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Common.ListFinLListEquiv where

open import lib.Base
open import lib.types.Nat using (_+_; O<S; <-ap-S; <-has-all-paths) renaming (_<_ to _<N_)
open import lib.types.Sigma
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.Equivalence
open import lib.types.List

open import Pi+.Extra
open import Pi+.Coxeter.Common.Arithmetic
open import Pi+.Coxeter.Common.InequalityEquiv
open import Pi+.Coxeter.Common.ListN renaming (_++_ to _++ℕ_)
open import Pi+.Coxeter.Common.LList


-- infixr 50 _+++_

-- _+++_ : {m : ℕ} -> (LList m) -> (LList m) -> LList m
-- (nil , nil) +++ r = r
-- ((x ∷ xs) , (.x :⟨ px ⟩: pxs)) +++ r = 
--   let rec = (xs , pxs) +++ r
--   in  (x ∷ rec .fst) , (x :⟨ px ⟩: rec .snd)

module _ {n : ℕ} where

  toLList : List (Fin n) -> (LList n)
  toLList nil = nil , nil
  toLList (x :: l) =
    let rec-l , rec-p = toLList l
    in  ((x . fst) ∷ rec-l) , ((x .fst) :⟨ –> <N≃< (x .snd) ⟩: rec-p)

  fromLList : (LList n) -> List (Fin n)
  fromLList (nil , nil) = nil
  fromLList ((x ∷ fst) , (.x :⟨ px ⟩: snd)) = (x , (<– <N≃< px)) :: fromLList (fst , snd)

  List≃LList : List (Fin n) ≃ (LList n)
  List≃LList = equiv toLList fromLList TODO TODO

  fromLList-++ : (l r : LList n) -> (fromLList l ++ fromLList r) == fromLList (((l .fst) ++ℕ (r .fst)) , (>>-++ (l .snd) (r .snd)))
  fromLList-++ (nil , nil) r = idp
  fromLList-++ ((x ∷ l) , (.x :⟨ x₁ ⟩: lp)) r = List=-out (idp , (fromLList-++ (l , lp) r))