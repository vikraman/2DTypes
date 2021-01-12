{-# OPTIONS --without-K --rewriting #-}

module Pi+.CoxeterNonParametrized.ImpossibleLists where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.CoxeterCommon.Arithmetic
open import Pi+.CoxeterCommon.Lists

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

-- TODO exact code duplication from incr-long-lemma
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


less-than-↓ : (n k o : ℕ) -> (k + n ≤ o) -> (l r : List) -> (n ↓ k) == (l ++ (o :: r)) -> ⊥
less-than-↓ n O o pko nil r ()
less-than-↓ n O o pko (x :: l) r ()
less-than-↓ n (S k) o pko nil r p = 1+n≰n (≤-trans pko (≤-reflexive (! (cut-tail p))))
less-than-↓ n (S k) o pko (x :: l) r p = less-than-↓ n k o (≤-down pko) l r (cut-head p) 

repeat-spaced-long-lemma : (n k o o1 : ℕ) -> (o ≤ o1) -> (l r1 r2 : List) -> (n ↓ k) == (l ++ (o :: r1) ++ (o1 :: r2)) -> ⊥
repeat-spaced-long-lemma n O o o1 op nil r1 r2 ()
repeat-spaced-long-lemma n O o o1 op (x :: l) r1 r2 ()
repeat-spaced-long-lemma n (S k) o o1 op nil r1 r2 p = 
  let k+n=o = cut-tail p 
  in  less-than-↓ n k o1 ((≤-trans (≤-reflexive (cut-tail p)) op)) r1 r2 (cut-head p)
repeat-spaced-long-lemma n (S k) o o1 op (x :: l) r1 r2 p = repeat-spaced-long-lemma n k o o1 op l r1 r2 (cut-head p)

repeat-spaced2-long-lemma : (n k n1 k1 n2 k2 o : ℕ) -> (S o < k1 + n1) -> (k2 + n2 ≤ o) -> (k + n < k1 + n1) -> (l r : List) -> (n ↓ k) ++ (n1 ↓ k1) == (l ++ (n2 ↓ S k2) ++ o :: r) -> ⊥
repeat-spaced2-long-lemma n O n1 k1 n2 O o op1 op2 pkn l r p = dec-long-lemma _ _ _ _ op2 _ _ p
repeat-spaced2-long-lemma n O n1 k1 n2 (S k2) o op1 op2 pkn l r p = repeat-spaced-long-lemma _ _ _ _ op2 _ (n2 ↓ (S k2)) r p
repeat-spaced2-long-lemma n (S O) n1 (S k1) n2 O o op1 op2 pkn nil r p = 
  let n=n2 = cut-tail p 
      k1+n1=o = cut-tail (cut-head p)
      open ≤-Reasoning
      lemma =
         S (S o)
        ≤⟨ op1 ⟩
          S (k1 + n1)
        ≡⟨ ap S k1+n1=o ⟩
          S o
        ≤∎

  in  1+n≰n lemma
repeat-spaced2-long-lemma n (S (S k)) n1 k1 n2 O o op1 op2 pkn nil r p = 
  let 1+k+n=n2 = cut-tail p 
      k+n=o = cut-tail (cut-head p)
  in  1+n≰n (≤-trans (≤-trans (≤-reflexive 1+k+n=n2) op2) (≤-reflexive (! k+n=o)))
repeat-spaced2-long-lemma n (S k) n1 k1 n2 (S k2) o op1 op2 pkn nil r p = repeat-spaced2-long-lemma n k n1 k1 n2 k2 o op1 (≤-down op2) (≤-down pkn) nil r (cut-head p)
repeat-spaced2-long-lemma n (S k) n1 k1 n2 k2 o op1 op2 pkn (x :: l) r p = repeat-spaced2-long-lemma n k n1 k1 n2 k2 o op1 op2 (≤-down pkn) l r (cut-head p)

repeat-↓-long-lemma-r : (n k n1 k1 n2 k2 : ℕ) -> (k + n < k1 + n1) -> (r : List) -> (n ↓ k) ++ (n1 ↓ k1) == ((n2 ↓ S k2) ++ (k2 + n2) :: r) -> ⊥
repeat-↓-long-lemma-r n O n1 k1 n2 k2 pkn r p = repeat-spaced-long-lemma n1 k1 (k2 + n2) (k2 + n2) (≤-reflexive idp) nil (n2 ↓ k2) r p
repeat-↓-long-lemma-r n (S k) n1 k1 n2 k2 pkn r p = 
  let lemma = cut-tail p
  in  repeat-spaced2-long-lemma n (S k) n1 k1 n2 k2 (k2 + n2) (≤-trans (≤-reflexive (ap (λ e -> S (S e)) (! lemma))) pkn) (≤-reflexive idp) pkn nil r p

repeat-↓-long-lemma : (n k n1 k1 n2 k2 : ℕ) -> (k + n < k1 + n1) -> (l r : List) -> (n ↓ k) ++ (n1 ↓ k1) == (l ++ (n2 ↓ S k2) ++ (k2 + n2) :: r) -> ⊥
repeat-↓-long-lemma n k n1 k1 n2 k2 pkn nil r p = repeat-↓-long-lemma-r n k n1 k1 n2 k2 pkn r p
repeat-↓-long-lemma n O n1 (S k1) n2 k2 pkn (x :: l) r p = repeat-spaced-long-lemma n1 k1 (k2 + n2) (k2 + n2) (≤-reflexive idp) l (n2 ↓ k2) r (cut-head p)
repeat-↓-long-lemma n (S k) n1 k1 n2 k2 pkn (x :: l) r p = repeat-↓-long-lemma n k n1 k1 n2 k2 (≤-trans (≤-down (≤-reflexive idp)) pkn) l r (cut-head p)

++-nonempty-abs : {n : ℕ} -> (l r : List) -> nil == l ++ n :: r -> ⊥
++-nonempty-abs {n} nil r = λ ()
++-nonempty-abs {n} (x :: l) r = λ ()