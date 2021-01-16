{-# OPTIONS --without-K --rewriting #-}

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
open import Pi+.Coxeter.Parametrized.Coxeter
open import Pi+.Coxeter.Parametrized.MCoxeter
open import Pi+.Coxeter.Parametrized.ReductionRel

-- lift-swap-lemma : {m : ℕ} -> {x : Fin (S m)} -> {l : List (Fin m)} -> 

{-# NON_TERMINATING #-}
long-swap-lemma : {m : ℕ} -> (n k : Fin m) -> (x : Fin (S m)) -> (S (S (n .fst)) < (x .fst)) -> (p : k ≤^ n) -> ((n ↓⟨ p ⟩ k) ++ (x :: nil)) ≈₁ (x :: (n ↓⟨ p ⟩ k))
long-swap-lemma n (O , kp) x nx p = comm (trans (respects-++ (swap nx) (idp {l = ⟨ n ⟩ :: nil})) (respects-++ (idp {l = S⟨ n ⟩ :: nil}) (swap (<-down nx))))
long-swap-lemma (O , snd₁) (S k , kp) x nx (ltSR ())
long-swap-lemma {S m} (S n , np) (S k , kp) x nx p =
    let rec = long-swap-lemma {S m} ⟨ n , <-cancel-S np ⟩ ⟨ k , <-cancel-S kp ⟩ x (<-down nx) (<-cancel-S p)
        lemma = (transport (λ e -> e ++ (x :: nil) ≈₁ x :: e) (! (map=⟨⟩ (n , <-cancel-S np) (k , <-cancel-S kp) (<-cancel-S p))) rec) -- 
    in  trans (respects-++ (idp {l = S⟨ (S n , np) ⟩ :: nil}) lemma) (respects-++ (comm (swap nx)) idp)

long-lemma : {m : ℕ} -> (n k : Fin m) -> (p : k ≤^ n) -> ((n ↓⟨ p ⟩ k) ++ (S⟨ n ⟩ :: nil)) ≈₁ (⟨ n ⟩ :: (n ↓⟨ p ⟩ k))
long-lemma n (O , _) p = braid
long-lemma (O , snd₁) (S k , kp) (ltSR ())
long-lemma {S m} (S O , np) (S .0 , kp) ltS = 
    let t = respects-++ braid (idp {S m} {l = ((O , O<S (S m))) :: nil})
    in  trans {!   !} {!   !}
long-lemma {S m} (S O , np) (S k , kp) (ltSR (ltSR ()))
long-lemma {S m} (S (S n) , np) (S k , kp) p = {!   !}

reduction->coxeter : {n : ℕ} -> {l1 l2 : List (Fin (S n))} -> (l1 ≅[ n ] l2) -> (l1 ≈₁ l2)
reduction->coxeter (cancelN≅ l r n) = respects-++ idp (respects-++ cancel idp)
reduction->coxeter (swapN≅ l r n k x) = respects-++ idp (respects-++ (swap x) idp)
reduction->coxeter (longN≅ l r n k p) = 
    let lemma = respects-++ (long-lemma n k p) (idp {l = r})
    in  respects-++ (idp {l = l}) (transport (λ e -> e ≈₁ (_ :: ((n ↓⟨ p ⟩ k) ++ r))) (++-assoc (n ↓⟨ p ⟩ k) (S⟨ n ⟩ :: nil) r) lemma)

reduction*->coxeter : {n : ℕ} -> (l1 l2 : List (Fin (S n))) -> (l1 ≅*[ n ] l2) -> (l1 ≈₁ l2)
reduction*->coxeter l1 .l1 idpN = idp
reduction*->coxeter l1 l2 (transN≅ x p) = trans (reduction->coxeter {l1 = l1} x) (reduction*->coxeter _ _ p)

mcoxeter->coxeter : {n : ℕ} -> (l1 l2 : List (Fin (S n))) -> (l1 ↔[ n ] l2) -> (l1 ≈₁ l2)
mcoxeter->coxeter l1 l2 (MC p1 p2) = trans (reduction*->coxeter _ _ p1) (comm (reduction*->coxeter _ _ p2))

coxeter->mcoxeter :  {n : ℕ} -> {l1 l2 : List (Fin (S n))} -> (l1 ≈₁ l2) -> l1 ↔[ n ] l2
coxeter->mcoxeter {n} (cancel {k}) = MC (extN (cancelN≅ nil nil k)) idpN
coxeter->mcoxeter {n} (swap x) = MC (extN (swapN≅ nil nil _ _ x)) idpN
coxeter->mcoxeter {S n} (braid {m , mp}) = MC (extN (longN≅ nil nil (m , mp) (O , O<S n) (O<S m))) idpN
coxeter->mcoxeter {n} idp = MC idpN idpN
coxeter->mcoxeter {n} (comm p) = comm↔ _ _ (coxeter->mcoxeter p)
coxeter->mcoxeter {n} (trans p p₁) = trans↔ _ _ _ (coxeter->mcoxeter p) (coxeter->mcoxeter p₁)
coxeter->mcoxeter {n} (respects-++ p p1) = ↔-respects-++ (coxeter->mcoxeter p) (coxeter->mcoxeter p1)
