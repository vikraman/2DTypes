{-# OPTIONS --without-K --rewriting #-}

module Pi+.Common.ListFinLListEquiv where

open import lib.Base
open import lib.types.Nat using (_+_; O<S; <-ap-S; <-has-all-paths) renaming (_<_ to _<N_)
open import lib.types.Sigma
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.Equivalence
open import lib.types.List

open import Pi+.Extra
open import  Pi+.Common.Arithmetic
open import  Pi+.Common.InequalityEquiv
open import  Pi+.Common.ListN renaming (_++_ to _++ℕ_)
open import  Pi+.Common.LList



module _ {n : ℕ} where

  toLList : List (Fin n) -> (LList n)
  toLList nil = nil , nil
  toLList (x :: l) =
    let rec-l , rec-p = toLList l
    in  ((x . fst) ∷ rec-l) , ((x .fst) :⟨ –> <N≃< (x .snd) ⟩: rec-p)

  fromLList : (LList n) -> List (Fin n)
  fromLList (nil , nil) = nil
  fromLList ((x ∷ fst) , (.x :⟨ px ⟩: snd)) = (x , (<– <N≃< px)) :: fromLList (fst , snd)

  abstract
    toLList∘fromLList : (l : LList n) → toLList (fromLList l) == l
    toLList∘fromLList (nil , nil) = idp
    toLList∘fromLList ((x ∷ l) , (.x :⟨ x₁ ⟩: lp)) =
      LList-eq (head+tail idp (ap fst (toLList∘fromLList (l , lp))))

    fromLList∘toLList : (l : List (Fin n)) → fromLList (toLList l) == l
    fromLList∘toLList nil = idp
    fromLList∘toLList ((x , xp) :: l) = List=-out ((pair= idp (<-has-all-paths _ xp)) , fromLList∘toLList l)

  List≃LList : List (Fin n) ≃ (LList n)
  List≃LList = equiv toLList fromLList toLList∘fromLList fromLList∘toLList

  fromLList-++ : (l r : LList n) -> (fromLList l ++ fromLList r) == fromLList (((l .fst) ++ℕ (r .fst)) , (>>-++ (l .snd) (r .snd)))
  fromLList-++ (nil , nil) r = idp
  fromLList-++ ((x ∷ l) , (.x :⟨ x₁ ⟩: lp)) r = List=-out (idp , (fromLList-++ (l , lp) r))

  fromLList-++-w : (l r m : LList n) -> ((l .fst) ++ℕ (r .fst) == m .fst) -> (fromLList l ++ fromLList r) == (fromLList m)
  fromLList-++-w l r m p =
    let m' = ((l .fst) ++ℕ (r .fst)) , (>>-++ (l .snd) (r .snd))
        lemma = LList-eq {_} {m'} {m} p
    in  fromLList-++ l r ∙ ap fromLList lemma

  toLList-++ : (l r : List (Fin n)) -> (toLList (l ++ r)) .fst == ((toLList l) .fst) ++ℕ ((toLList r) .fst)
  toLList-++ nil r = idp
  toLList-++ (x :: l) r =
    let rec = toLList-++ l r
    in  head+tail idp rec

  rev-reverse : (l : List (Fin n)) -> LList-rev (toLList (reverse l)) == (toLList l)
  rev-reverse nil = idp
  rev-reverse (x :: l) =
    let rec = rev-reverse l
    in  LList-eq ((ap rev (toLList-++ (reverse l) (x :: nil)) ∙ rev-++ (fst (toLList (reverse l))) ((x .fst) ∷ nil)) ∙ head+tail idp (ap fst rec))
