{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.CritPairsImpossible where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.Coxeter.Arithmetic
open import Pi+.Coxeter.Lists
open import Pi+.Coxeter.ReductionRel
open import Pi+.Coxeter.CritPairsSwap

open ≅*-Reasoning

repeat-long-lemma : (n k n1 : ℕ) -> (l r : List) -> (n ↓ k) == (l ++ n1 :: n1 :: r) -> ⊥
repeat-long-lemma n 0 n1 nil r ()
repeat-long-lemma n 0 n1 (x :: l) r ()
repeat-long-lemma n (S (S k)) n1 nil r p =
  abs-refl (≤-trans (≤-reflexive (cut-t1 p)) (≤-reflexive (≡-sym (cut-t2 p))))
repeat-long-lemma n (S k) n1 (x :: l) r p = repeat-long-lemma n k n1 l r (cut-head p)

repeat-long-lemma-rev : (n k n1 : ℕ) -> (l r : List) -> (n ↑ k) == (l ++ n1 :: n1 :: r) -> ⊥
repeat-long-lemma-rev n 0 n1 nil r ()
repeat-long-lemma-rev n 0 n1 (x :: l) r ()
repeat-long-lemma-rev n (S 0) n1 nil r ()
repeat-long-lemma-rev n (S (S k)) n1 nil r ()
repeat-long-lemma-rev n (S k) n1 (x :: l) r p = repeat-long-lemma-rev (S n) k n1 l r (cut-head p)


incr-long-lemma-rev : (n k n1 k1 : ℕ) -> (S k1 < n1) -> (l r : List) -> (n ↑ k) == (l ++ k1 :: n1 :: r) -> ⊥
incr-long-lemma-rev n (S (S k)) .(S n) .n pkn nil .(S (S n) ↑ k) idp = abs-refl pkn
incr-long-lemma-rev n (S k) n1 k1 pkn (x :: l) r p = incr-long-lemma-rev (S n) k n1 k1 pkn l r (cut-head p)


incr-long-lemma : (n k n1 k1 : ℕ) -> (S k1 < n1) -> (l r : List) -> (n ↓ k) == (l ++ n1 :: k1 :: r) -> ⊥
incr-long-lemma n k n1 k1 p l r q =
  let pp =
        begin
          (n ↑ k)
        =⟨ ≡-sym (rev-d n k) ⟩
          rev (n ↓ k)
        =⟨ cong rev q ⟩
          rev (l ++ n1 :: k1 :: r)
        =⟨ rev-++ l (n1 :: k1 :: r) ⟩
          ((rev r ++ k1 :: nil) ++ n1 :: nil) ++ rev l
        =⟨ ++-assoc (rev r ++ k1 :: nil) (n1 :: nil) (rev l) ⟩
          (rev r ++ k1 :: nil) ++ n1 :: rev l
        =⟨ ++-assoc (rev r) (k1 :: nil) (n1 :: rev l) ⟩
          rev r ++ k1 :: n1 :: rev l
        =∎
  in  incr-long-lemma-rev n k n1 k1 p (rev r) (rev l) pp

dec-long-lemma-rev : (n k n1 k1 : ℕ) -> (n1 ≤ k1) -> (l r : List) -> (n ↑ k) == (l ++ k1 :: n1 :: r) -> ⊥
dec-long-lemma-rev n (S (S k)) .(S n) .n pkn nil .(S (S n) ↑ k) idp = abs-refl pkn
dec-long-lemma-rev n (S k) n1 k1 pkn (x :: l) r p = dec-long-lemma-rev (S n) k n1 k1 pkn l r (cut-head p)

-- TODO exact code duplication from iincr-long-lemma
dec-long-lemma : (n k n1 k1 : ℕ) -> (n1 ≤ k1) -> (l r : List) -> (n ↓ k) == (l ++ n1 :: k1 :: r) -> ⊥
dec-long-lemma n k n1 k1 p l r q =
  let pp =
        begin
          (n ↑ k)
        =⟨ ≡-sym (rev-d n k) ⟩
          rev (n ↓ k)
        =⟨ cong rev q ⟩
          rev (l ++ n1 :: k1 :: r)
        =⟨ rev-++ l (n1 :: k1 :: r) ⟩
          ((rev r ++ k1 :: nil) ++ n1 :: nil) ++ rev l
        =⟨ ++-assoc (rev r ++ k1 :: nil) (n1 :: nil) (rev l) ⟩
          (rev r ++ k1 :: nil) ++ n1 :: rev l
        =⟨ ++-assoc (rev r) (k1 :: nil) (n1 :: rev l) ⟩
          rev r ++ k1 :: n1 :: rev l
        =∎
  in  dec-long-lemma-rev n k n1 k1 p (rev r) (rev l) pp

postulate
  repeat-spaced-long-lemma : (n k n1 : ℕ) -> (l r1 r2 : List) -> (n ↓ k) == (l ++ n1 :: r1 ++ n1 :: r2) -> ⊥
