{-# OPTIONS --without-K --rewriting #-}

module Pi+.UFin.Equiv where

open import lib.Base
open import lib.Univalence
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.PathGroupoid
open import lib.PathOver
open import lib.types.Fin
open import lib.types.List
open import lib.types.Sigma
open import lib.types.Truncation
open import lib.types.Nat

open import Pi+.Misc
open import Pi+.UFin.Base

f : {n : ℕ} -> Ω (UFin , FinFS n) -> Aut (Fin n)
f {n} x = coe-equiv (fst= x)

g : {n : ℕ} -> Aut (Fin n) -> Ω (UFin , FinFS n)
g x = FinSet= (ua x)

f-g : {n : ℕ} -> (x : Aut (Fin n)) -> f(g x) == x
f-g {n} x =
    let lemma : [ n , idp ] == [ n , idp ] [ (SubtypeProp.prop FinSet-prop) ↓ (ua x)]
        lemma = prop-has-all-paths-↓

        t1 : coe-equiv (fst= (pair= (ua x) _)) == coe-equiv (ua x)
        t1 = ap coe-equiv (fst=-β (ua x) lemma)

        t2 : coe-equiv (ua x) == x
        t2 = coe-equiv-β x
    in  t1 ∙  t2

lemma : {n : ℕ} -> {x y : Fin n == Fin n} ->
        (p : [ n , idp ] == [ n , idp ] [ (SubtypeProp.prop FinSet-prop) ↓ x ]) -> 
        (q : [ n , idp ] == [ n , idp ] [ (SubtypeProp.prop FinSet-prop) ↓ y ]) -> 
        (x == y) -> pair= x p == pair= y q
lemma = {!   !}

g-f : {n : ℕ} -> (x : Ω (UFin , FinFS n)) -> g(f x) == x
g-f {n} x =
    let t1 : (ua (coe-equiv (fst= x))) == (fst= x)
        t1 = ua-η (fst= x)

        t2 : pair= (ua (coe-equiv (fst= x))) prop-has-all-paths-↓ == pair= (fst= x) prop-has-all-paths-↓
        t2 = lemma _ _ t1

        t3 : pair= (fst= x) prop-has-all-paths-↓ == x
        t3 = lemma _ (snd= x) idp ∙ ! (pair=-η x)
        
    in  t2 ∙ t3

UFin≃Fin : {n : ℕ} -> Ω (UFin , FinFS n) ≃ Aut (Fin n)
UFin≃Fin = equiv f g f-g g-f
