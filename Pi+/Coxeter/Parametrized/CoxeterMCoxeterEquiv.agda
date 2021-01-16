{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

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

  
long-swap-lemma : {m : ℕ} -> (n k : Fin m) -> (x : Fin (S m)) -> ((n .fst) < (x .fst)) -> (p : k ≤^ n) -> ((n ↓⟨ p ⟩ k) ++ (x :: nil)) ≈₁ (x :: (n ↓⟨ p ⟩ k))
long-swap-lemma n (O , kp) x nx p = {! snd₁ !}
long-swap-lemma n (S k , kp) x nx p = {!   !}

-- long-lemma : (n k : ℕ) -> ((n ↓ (2 + k)) ++ S (k + n) ∷ nil) ~ (k + n ∷ (n ↓ (2 + k)))
-- long-lemma n 0 = braid~
-- long-lemma n (S k) = trans~ (respects-l~ (_ ∷ _ ∷ nil) (long-swap-lemma n (1 + k) (2 + k + n) rrr) idp idp) (respects-r~ _ braid~ idp idp)

-- mcoxeter≅->coxeter : (m1 m2 : List) -> (m1 ≅ m2) -> (m1 ~ m2)
-- mcoxeter≅->coxeter m1 m2 (cancel≅ l r .m1 .m2 defm defmf) = respects-l~ l (respects-r~ r cancel~ idp idp) defm defmf
-- mcoxeter≅->coxeter m1 m2 (swap≅ x l r .m1 .m2 defm defmf) = respects-l~ l (respects-r~ r (swap~ x) idp idp) defm defmf
-- mcoxeter≅->coxeter m1 m2 (long≅ {n} k nil r .m1 .m2 defm defmf) = respects-r~ r (long-lemma n k) (≡-trans defm (≡-sym (++-assoc (n ↓ (2 + k)) [ 1 + k + n ] r))) defmf
-- mcoxeter≅->coxeter (x₁ ∷ m1) (x₂ ∷ m2) (long≅ k (x ∷ l) r .(x₁ ∷ m1) .(x₂ ∷ m2) defm defmf) =
--   let rec = mcoxeter≅->coxeter m1 m2 (long≅ k l r m1 m2 (cut-head defm) (cut-head defmf))
--   in  respects-l~ [ x ] rec (head+tail (cut-tail defm) idp) (head+tail (cut-tail defmf) idp)

-- mcoxeter≅*->coxeter : (m1 m2 : List) -> (m1 ≅* m2) -> (m1 ~ m2)
-- mcoxeter≅*->coxeter m1 .m1 idp = idp~
-- mcoxeter≅*->coxeter m1 m2 (trans≅ x p) = trans~ ((mcoxeter≅->coxeter _ _ x)) ((mcoxeter≅*->coxeter _ _ p))

reduction->coxeter : {n : ℕ} -> (l1 l2 : List (Fin (S n))) -> (l1 ≅[ n ] l2) -> (l1 ≈₁ l2)
reduction->coxeter .(l ++ (n :: n :: r)) .(l ++ r) (cancelN≅ l r n) = respects-++ idp (respects-++ cancel idp)
reduction->coxeter .(l ++ (n :: k :: r)) .(l ++ (k :: n :: r)) (swapN≅ l r n k x) = respects-++ idp (respects-++ (swap x) idp)
reduction->coxeter .((n ↓⟨ p ⟩ k) ++ ((S (fst n) , <-ap-S (snd n)) :: r)) .((fst n , ltSR (snd n)) :: (n ↓⟨ p ⟩ k) ++ r) (longN≅ nil r n k p) = {!   !}
reduction->coxeter .(x :: l ++ (n ↓⟨ p ⟩ k) ++ ((S (fst n) , <-ap-S (snd n)) :: r)) .(x :: l ++ ((fst n , ltSR (snd n)) :: (n ↓⟨ p ⟩ k) ++ r)) (longN≅ (x :: l) r n k p) = {!   !} 

reduction*->coxeter : {n : ℕ} -> (l1 l2 : List (Fin (S n))) -> (l1 ≅*[ n ] l2) -> (l1 ≈₁ l2)
reduction*->coxeter l1 .l1 idpN = idp
reduction*->coxeter l1 l2 (transN≅ x p) = trans (reduction->coxeter l1 _ x) (reduction*->coxeter _ _ p)

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
