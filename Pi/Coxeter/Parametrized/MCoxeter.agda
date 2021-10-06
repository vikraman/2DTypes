{-# OPTIONS --without-K --rewriting #-}

module Pi.Coxeter.Parametrized.MCoxeter where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid
open import lib.types.List
open import lib.types.Fin
open import lib.Equivalence

open import Pi.Common.Misc
open import Pi.Common.ListFinLListEquiv
open import Pi.Coxeter.Parametrized.ReductionRel
open import Pi.Coxeter.NonParametrized.Diamond


syntax MCoxeterN n l1 l2 = l1 ↔[ n ] l2

-- Using ReductionRel to define a symmetric relation - l1 and l2 are related if there is a cospan
-- l1 ← v → l2
data MCoxeterN : (m : ℕ) -> List (Fin (S m)) -> List (Fin (S m)) -> Set where
  MC : {m : ℕ} -> {l1 l2 lf : List (Fin (S m))} -> (p1 : l1 ≅*[ m ] lf) -> (p2 : l2 ≅*[ m ] lf) -> l1 ↔[ m ] l2

refl↔ : {m : ℕ} -> (l : List (Fin (S m))) -> (l ↔[ m ] l)
refl↔ m = MC idpN idpN

comm↔ : {m : ℕ} -> (l1 l2 : List (Fin (S m))) -> (l1 ↔[ m ] l2) -> (l2 ↔[ m ] l1)
comm↔ l1 l2 (MC p1 p2) = MC p2 p1

-- to prove that MC is indeed transitive, we need diamond lemma
abstract
  trans↔ : {m : ℕ} -> (l1 l2 l3 : List (Fin (S m))) -> (r1 : l1 ↔[ m ] l2) -> (r2 : l2 ↔[ m ] l3) -> (l1 ↔[ m ] l3)
  trans↔ {m} l1 l2 l3 (MC {lf = lf1} p1 p2) (MC {lf = lf2} p3 p4) =
    let ll1 , ll1-p = –> List≃LList l1
        ll2 , ll2-p = –> List≃LList l2
        ll3 , ll3-p = –> List≃LList l3
        llf1 , llf1-p = –> List≃LList lf1
        llf2 , llf2-p = –> List≃LList lf2

        p2u = reduction-toLList* _ _ p2
        p3u = reduction-toLList* _ _ p3
        lemma-m , lemma1 , lemma2 = diamond-full p2u p3u
        lemma-m-p = reduction-implies->> ((llf1 , llf1-p)) lemma-m lemma1
        lemma-m-f = <– List≃LList (lemma-m , lemma-m-p)
        lemma1u = reduction-fromLList* (llf1 , llf1-p) (lemma-m , lemma-m-p) lemma1
        lemma2u = reduction-fromLList* (llf2 , llf2-p) (lemma-m , lemma-m-p) lemma2
        leg1 = transN p1 (transport (λ e -> ReductionRel* m e lemma-m-f) (fromLList∘toLList lf1) lemma1u)
        leg2 = transN p4 (transport (λ e -> ReductionRel* m e lemma-m-f) (fromLList∘toLList lf2) lemma2u)
    in  MC leg1 leg2

↔-respects-++ : {m : ℕ} -> {l l' r r' : List (Fin (S m))} -> (l ↔[ m ] l') -> (r ↔[ m ] r') -> ((l ++ r) ↔[ m ] (l' ++ r'))
↔-respects-++ (MC p1 p2) (MC p3 p4) = MC (reduction*-respects-++ p1 p3) (reduction*-respects-++ p2 p4)
