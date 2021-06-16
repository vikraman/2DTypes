{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

module Pi+.Coxeter.Parametrized.CoxeterMCoxeterEquiv where

open import lib.Base
open import lib.types.Nat
open import lib.types.Sigma
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.Equivalence
open import lib.types.List

open import Pi+.Misc
open import Pi+.Extra
open import Pi+.Common.ListFinLListEquiv
open import Pi+.Common.FinHelpers
open import Pi+.Common.LList
open import Pi+.Coxeter.Coxeter
open import Pi+.Coxeter.Parametrized.MCoxeter
open import Pi+.Coxeter.Parametrized.ReductionRel

long-swap-lemmaH : {m : ℕ} -> (n k : ℕ) -> (np : n < m) -> (kp : k < m) -> (x : Fin (S m)) -> (S (S n) < (x .fst)) -> (p : k < S n) 
    -> (((n , np) ↓⟨ p ⟩ (k , kp)) ++ (x :: nil)) ≈* (x :: ((n , np) ↓⟨ p ⟩ (k , kp)))
long-swap-lemmaH {S m} n O np kp x nx p = 
    comm (trans (respects-++ (≈-rel $ swap nx) (idp {l = ⟨ (n , np) ⟩ :: nil})) (respects-++ (idp {l = S⟨ (n , np) ⟩ :: nil}) (≈-rel $ swap (<-down nx))))
long-swap-lemmaH {S m} O (S k) np kp x nx (ltSR ())
long-swap-lemmaH {S m} (S n) (S k) np kp x nx p = 
    let rec = long-swap-lemmaH {S m} n k (<-down np) (<-down kp) x (<-down nx) (<-cancel-S p)
        one = respects-++ (≈-rel $ swap nx) (idp {l = (n , (<-down np)) ↓⟨ (<-cancel-S p) ⟩ (k , (<-down kp))})
        two = respects-++ (idp {l = (S (S n) , <-ap-S np) :: nil}) (comm rec)
    in  comm (trans one two)

long-swap-lemma : {m : ℕ} -> (n k : Fin m) -> (x : Fin (S m)) -> (S (S (n .fst)) < (x .fst)) -> (p : k ≤^ n) -> ((n ↓⟨ p ⟩ k) ++ (x :: nil)) ≈* (x :: (n ↓⟨ p ⟩ k))
long-swap-lemma {S m} (n , np) (k , kp) x nx p = long-swap-lemmaH n k np kp x nx p

ListFin-eq : {m : ℕ} -> {l1 l2 : List (Fin (S m))} -> ((–> List≃LList l1) .fst) == ((–> List≃LList l2) .fst) -> l1 == l2
ListFin-eq {m1} {l1} {l2} p = 
    let ll = LList-eq p
    in  ! (fromLList∘toLList l1) ∙ ap fromLList ll ∙ fromLList∘toLList l2

long-lemma : {m : ℕ} -> (n k : Fin m) -> (p : k ≤^ n) -> ((n ↓⟨ p ⟩ k) ++ (S⟨ n ⟩ :: nil)) ≈* (⟨ n ⟩ :: (n ↓⟨ p ⟩ k))
long-lemma n (O , kp) p = ≈-rel $ braid
long-lemma {S m} (O , np) (S O , kp) (ltSR ())
long-lemma {m} (S n , np) (S O , kp) p = 
    let t = respects-++ (≈-rel (braid {m} {(S n) , np})) idp -- respects-++ (braid {S m} {(S n , np)}) (idp {S m} {l = (n , ltSR (ltSR (<-cancel-S np))) :: nil})
        t2 = trans (respects-++ (idp {l = _ :: _ :: nil}) (comm (≈-rel $ swap {m} {_} {n , (<-down (<-down (<-ap-S np)))} ltS))) t 
    in  transport2 (λ e f -> e ≈* f) (ListFin-eq idp) (ListFin-eq idp) t2
long-lemma {S m} (O , np) (S (S k) , kp) (ltSR ())
long-lemma {S O} (S O , np) (S (S k) , kp) (ltSR (ltSR ()))
long-lemma {S (S m)} (S O , np) (S (S k) , kp) (ltSR (ltSR ()))
long-lemma {S O} (S (S n) , np) (S (S k) , ltSR ()) p
long-lemma {S m} (S (S n) , np) (S (S k) , kp) p = 
    let t1 = respects-++ (idp {l = _ :: _ :: nil}) (long-swap-lemma _ (k , (<-down (<-down kp))) _ ltS _)
        t2 = respects-++ (≈-rel $ braid {n = (S (S n)) , np}) idp -- respects-++ (braid {n = (S (S n)) , np}) (idp {l = (n , _) ↓⟨ cc p ⟩ (k , <-down (<-down kp))})
        t = trans t1 t2
    in  transport2 (λ e f -> e ≈* f) (ListFin-eq idp) (ListFin-eq idp) t

reduction->coxeter : {n : ℕ} -> {l1 l2 : List (Fin (S n))} -> (l1 ≅[ n ] l2) -> (l1 ≈* l2)
reduction->coxeter (cancelN≅ l r n) = respects-++ idp (respects-++ (≈-rel cancel) idp)
reduction->coxeter (swapN≅ l r n k x) = respects-++ idp (respects-++ (≈-rel $ swap x) idp)
reduction->coxeter (longN≅ l r n k p) = 
    let lemma = respects-++ (long-lemma n k p) (idp {l = r})
    in  respects-++ (idp {l = l}) (transport (λ e -> e ≈* (_ :: ((n ↓⟨ p ⟩ k) ++ r))) (++-assoc (n ↓⟨ p ⟩ k) (S⟨ n ⟩ :: nil) r) lemma)

reduction*->coxeter : {n : ℕ} -> (l1 l2 : List (Fin (S n))) -> (l1 ≅*[ n ] l2) -> (l1 ≈* l2)
reduction*->coxeter l1 .l1 idpN = idp
reduction*->coxeter l1 l2 (transN≅ x p) = trans (reduction->coxeter {l1 = l1} x) (reduction*->coxeter _ _ p)

mcoxeter->coxeter : {n : ℕ} -> (l1 l2 : List (Fin (S n))) -> (l1 ↔[ n ] l2) -> (l1 ≈* l2)
mcoxeter->coxeter l1 l2 (MC p1 p2) = trans (reduction*->coxeter _ _ p1) (comm (reduction*->coxeter _ _ p2))

coxeter->mcoxeter :  {n : ℕ} -> {l1 l2 : List (Fin (S n))} -> (l1 ≈* l2) -> l1 ↔[ n ] l2
coxeter->mcoxeter {n} (≈-rel (cancel {k})) = MC (extN (cancelN≅ nil nil k)) idpN
coxeter->mcoxeter {n} (≈-rel (swap x)) = MC (extN (swapN≅ nil nil _ _ x)) idpN
coxeter->mcoxeter {S n} (≈-rel (braid {m , mp})) = 
    MC (extN (longN≅ nil nil (m , mp) (O , O<S n) (O<S m))) idpN -- MC (extN (longN≅ nil nil (m , mp) (O , O<S n) (O<S m))) idpN
coxeter->mcoxeter {n} idp = MC idpN idpN
coxeter->mcoxeter {n} (comm p) = comm↔ _ _ (coxeter->mcoxeter p)
coxeter->mcoxeter {n} (trans p p₁) = trans↔ _ _ _ (coxeter->mcoxeter p) (coxeter->mcoxeter p₁)
coxeter->mcoxeter {n} (respects-++ p p1) = ↔-respects-++ (coxeter->mcoxeter p) (coxeter->mcoxeter p1)
