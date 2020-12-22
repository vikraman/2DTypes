{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Diamond where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.Coxeter.Arithmetic
open import Pi+.Coxeter.Lists
open import Pi+.Coxeter.MCoxeter
open import Pi+.Coxeter.CritPairsSwap
open import Pi+.Coxeter.CritPairsImpossible
open import Pi+.Coxeter.CritPairsLong

open ≅*-Reasoning

-- and this should do something like: if ir1 = (ir p1) and ir2 = (ir p2) are non-overlapping, use force-non-crit-pair
-- otherwise, take the ir1 ∪ ir2 , force it into one of the critical pairs and then reduce critical pair
{-# NON_TERMINATING #-}
diamond : (m1 m2 m3 : List) -> (m1 ≅ m2) -> (m1 ≅ m3) -> Σ _ (λ m -> (m2 ≅* m) × (m3 ≅* m))
-- -- crit-pair
diamond (x₁ :: .x₁ :: .x₁ :: m1) m2 m3 (cancel≅ nil .(x₁ :: m1) .(x₁ :: x₁ :: x₁ :: m1) .m2 idp defmf) (cancel≅ (.x₁ :: nil) .m1 .(x₁ :: x₁ :: x₁ :: m1) .m3 idp defmf₁)
  rewrite defmf rewrite defmf₁ = (x₁ :: m1) , (idp , idp) -- cc
diamond (x₂ :: .x₂ :: x₄ :: m1) m2 m3 (cancel≅ nil .(x₄ :: m1) .(x₂ :: x₂ :: x₄ :: m1) .m2 idp defmf) (swap≅ x (.x₂ :: nil) .m1 .(x₂ :: x₂ :: x₄ :: m1) .m3 idp defmf₁)
  rewrite defmf rewrite defmf₁ = (x₄ :: m1) , (idp , trans (swap x nil _) (cancel [ x₄ ] m1)) -- cs
diamond (c :: b :: a :: m1) m2 m3 (swap≅ b<c nil .(a :: m1) .(c :: b :: a :: m1) .m2 idp defmf) (swap≅ a<b (.c :: nil) .m1 .(c :: b :: a :: m1) .m3 idp defmf₁)
  rewrite defmf rewrite defmf₁ =
  let a<c : S a < c
      a<c = ≤-down (≤-trans (s≤s a<b) (≤-down b<c))
      left = trans (swap a<c [ b ] m1) (swap a<b nil _)
      right = trans (swap a<c nil _) (swap b<c [ a ] _)
   in (a :: b :: c :: m1) , (left , right) -- ss
diamond (x₂ :: x₃ :: .x₃ :: m1) m2 m3 (cancel≅ (.x₂ :: nil) .m1 .(x₂ :: x₃ :: x₃ :: m1) .m2 idp defmf) (swap≅ x nil .(x₃ :: m1) .(x₂ :: x₃ :: x₃ :: m1) .m3 idp defmf₁)
  rewrite defmf rewrite defmf₁ = _ , (idp , trans (swap x [ x₃ ] _) (cancel nil _)) -- cs
diamond m1 m2 m3 (long≅ {n} k1 nil r m mf defm defmf) (long≅ {n₁} k2 nil r₁ m₁ mf₁ defm₁ defmf₁)
  rewrite defmf rewrite defmf₁ rewrite (cut-t2 (≡-trans (≡-sym defm) defm₁)) =
  let eq = ≡-trans (≡-sym defm) defm₁
      eqn , eql , eqr = long-lemma n n₁ k1 k2 _ _ (s≤s (≤-up-+ (≤-reflexive idp))) (s≤s (≤-up-+ (≤-reflexive idp))) r r₁ eq
  in  _ , (idp , idp≅* (head+tail idp (start+end (head+tail idp (head+tail idp (≡-sym (cut-h2 eql)))) (≡-sym eqr))))
diamond .(S (k + _) :: S (k + _) :: k + _ :: (_ ↓ k) ++ S (k + _) :: r₁) m2 m3 (cancel≅ nil .(k + _ :: (_ ↓ k) ++ S (k + _) :: r₁) .(S (k + _) :: S (k + _) :: k + _ :: (_ ↓ k) ++ S (k + _) :: r₁) .m2 idp defmf) (long≅ {n} k (.(S (k + _)) :: nil) r₁ .(S (k + _) :: S (k + _) :: k + _ :: (_ ↓ k) ++ S (k + _) :: r₁) .m3 idp defmf₁) rewrite defmf rewrite defmf₁ =
  let right =
        ≅*begin
          S (k + n) :: k + n :: S (k + n) :: k + n :: (n ↓ k) ++ r₁
        ≅*⟨ braid nil _ ⟩
          k + n :: S (k + n) :: k + n :: k + n :: (n ↓ k) ++ r₁
        ≅*⟨ cancel (k + n :: S (k + n) :: nil) ((n ↓ k) ++ r₁) ⟩
          k + n :: S (k + n) :: (n ↓ k) ++ r₁
        ≅*⟨ long-swap-lr n (S (k + n)) k [ _ ] r₁ rrr ⟩
          k + n :: (n ↓ k) ++ S (k + n) :: r₁
        ≅*∎
  in  _ , (idp , right)
diamond .(x :: S (k + _) :: k + _ :: (_ ↓ k) ++ S (k + _) :: r₁) m2 m3 (swap≅ p nil .(k + _ :: (_ ↓ k) ++ S (k + _) :: r₁) .(x :: S (k + _) :: k + _ :: (_ ↓ k) ++ S (k + _) :: r₁) .m2 idp defmf) (long≅ {n} k (x :: nil) r₁ .(x :: S (k + _) :: k + _ :: (_ ↓ k) ++ S (k + _) :: r₁) .m3 idp defmf₁) rewrite defmf rewrite defmf₁ =
  let left =
        ≅*begin
          S (k + n) :: x :: k + n :: (n ↓ k) ++ S (k + n) :: r₁
        ≅*⟨ long-swap-lr n x (S k) [ _ ] (S (k + n) :: r₁) (≤-down p) ⟩
          S (k + n) :: k + n :: (n ↓ k) ++ x :: S (k + n) :: r₁
        ≅*⟨ swap p (S (k + n) :: k + n :: (n ↓ k)) r₁ ⟩
          S (k + n) :: k + n :: (n ↓ k) ++ S (k + n) :: x :: r₁
        ≅*⟨ long k nil (x :: r₁) ⟩
          k + n :: S (k + n) :: k + n :: (n ↓ k) ++ x :: r₁
        ≅*∎
      right =
        ≅*begin
          x :: k + n :: (n ↓ (2 + k)) ++ r₁
        ≅*⟨ swap (≤-down p) nil ((n ↓ (2 + k)) ++ r₁) ⟩
         k + n :: x :: S (k + n) :: k + n :: (n ↓ k) ++ r₁
        ≅*⟨ long-swap-lr n x (S (S k)) [ _ ] r₁ p ⟩
          k + n :: S (k + n) :: k + n :: (n ↓ k) ++ x :: r₁
        ≅*∎
  in  _ , (left , right)
-- -- -- - disjoint
diamond .(_ :: _ :: r) m2 m3 (cancel≅ nil r .(_ :: _ :: r) .m2 idp defmf) (cancel≅ {n = n} (x :: x₁ :: l) r₁ .(_ :: _ :: r) .m3 d defmf₁)
    rewrite (≡-trans defmf (cut-h2 d)) rewrite defmf₁ rewrite (≡-sym (cut-t1 d)) rewrite (≡-sym (cut-t2 d)) =
    (l ++ r₁) ,  cancel l r₁ , (cancel nil (l ++ r₁)) --((cancel l r₁) ,  -- cc-dis
diamond .(_ :: _ :: r) m2 m3 (cancel≅ nil r .(_ :: _ :: r) .m2 idp defmf) (swap≅ x (x₁ :: x₂ :: l) r₁ .(_ :: _ :: r) .m3 d defmf₁)
    rewrite (≡-trans defmf (cut-h2 d)) rewrite defmf₁ rewrite (≡-sym (cut-t1 d)) rewrite (≡-sym (cut-t2 d)) =
     ((l ++ _ :: _ :: r₁)) , (swap x l r₁ , cancel nil _) -- cs-dis
diamond .(_ :: _ :: r) m2 m3 (swap≅ x nil r .(_ :: _ :: r) .m2 idp defmf) (swap≅ x₁ (x₂ :: x₃ :: l) r₁ .(_ :: _ :: r) .m3 d defmf₁)
    rewrite defmf rewrite defmf₁ rewrite (≡-sym (cut-t1 d)) rewrite (≡-sym (cut-t2 d)) rewrite (cut-h2 d) =
     _ , (swap x₁ (_ :: _ :: l) r₁ , swap x nil (l ++ _ :: _ :: r₁)) -- ss-dis
diamond .(_ :: _ :: r₁) m2 m3 (cancel≅ (x₁ :: x₂ :: l) r .(_ :: _ :: r₁) .m2 defm defmf) (swap≅ x nil r₁ .(_ :: _ :: r₁) .m3 idp defmf₁)
  rewrite defmf rewrite defmf₁ rewrite (cut-h2 defm) rewrite ≡-sym (cut-t1 defm) rewrite ≡-sym (cut-t2 defm) =
  _ , (swap x nil _ , cancel _ r)

diamond .(_ :: _ :: r) m2 m3 (cancel≅ nil r .(_ :: _ :: r) .m2 idp defmf) (long≅ k (x :: x₁ :: l₁) r₁ .(_ :: _ :: r) .m3 d defmf₁)
  rewrite defmf rewrite defmf₁ rewrite (cut-h2 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) =
  _ , ((long k l₁ r₁) , (cancel nil _))
diamond .(_ :: _ :: r) m2 m3 (swap≅ x nil r .(_ :: _ :: r) .m2 idp defmf) (long≅ k (x₁ :: x₂ :: l₁) r₁ .(_ :: _ :: r) .m3 d defmf₁)
  rewrite defmf rewrite defmf₁ rewrite (cut-h2 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) =
  _ , ((long k (_ :: _ :: l₁) r₁) , (swap x nil _))

-- --- identity
diamond .(_ :: _ :: r) m2 m3 (cancel≅ nil r .(_ :: _ :: r) .m2 idp defmf) (cancel≅ nil r₁ .(_ :: _ :: r) .m3 defm₁ defmf₁)
  rewrite defmf rewrite defmf₁ rewrite (cut-h2 defm₁)  = r₁ , (idp , idp)
diamond .(_ :: _ :: r) m2 m3 (swap≅ x nil r .(_ :: _ :: r) .m2 idp defmf) (swap≅ x₁ nil r₁ .(_ :: _ :: r) .m3 defm₁ defmf₁)
  rewrite defmf rewrite defmf₁ rewrite (cut-h2 defm₁) rewrite (cut-t1 defm₁) rewrite (cut-t2 defm₁)  = _ , (idp , idp)

-- --- rec
diamond m1 m2 m3 (swap≅ x l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) =
  let rec-m , rec-l , rec-r = diamond m1 m3 m2 (cancel≅ l₁ r₁ m1 m3 defm₁ defmf₁) (swap≅ x l r m1 m2 defm defmf)
  in  rec-m , rec-r , rec-l
diamond m1 m2 m3 (long≅ k l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) =
  let rec-m , rec-l , rec-r = diamond m1 m3 m2 (cancel≅ l₁ r₁ m1 m3 defm₁ defmf₁) (long≅ k l r m1 m2 defm defmf)
  in  rec-m , rec-r , rec-l
diamond m1 m2 m3 (long≅ k l r .m1 .m2 defm defmf) (swap≅ x l₁ r₁ .m1 .m3 defm₁ defmf₁) =
  let rec-m , rec-l , rec-r = diamond m1 m3 m2 (swap≅ x l₁ r₁ m1 m3 defm₁ defmf₁) (long≅ k l r m1 m2 defm defmf)
  in  rec-m , rec-r , rec-l

diamond m1 m2 m3 (cancel≅ (x :: l) r .m1 .m2 defm defmf) (cancel≅ nil r₁ .m1 .m3 defm₁ defmf₁) =
  let rec-m , rec-l , rec-r = diamond m1 m3 m2 (cancel≅ nil r₁ m1 m3 defm₁ defmf₁) (cancel≅ (x :: l) r m1 m2 defm defmf)
  in  rec-m , rec-r , rec-l
diamond m1 m2 m3 (swap≅ x (x₂ :: l) r .m1 .m2 defm defmf) (swap≅ x₁ nil r₁ .m1 .m3 defm₁ defmf₁) =
  let rec-m , rec-l , rec-r = diamond m1 m3 m2 (swap≅ x₁ nil r₁ m1 m3 defm₁ defmf₁) (swap≅ x (x₂ :: l) r m1 m2 defm defmf)
  in  rec-m , rec-r , rec-l
diamond m1 m2 m3 (long≅ k (x :: l) r .m1 .m2 defm defmf) (long≅ k₁ nil r₁ .m1 .m3 defm₁ defmf₁) =
  let rec-m , rec-l , rec-r = diamond m1 m3 m2 (long≅ k₁ nil r₁ m1 m3 defm₁ defmf₁) (long≅ k (x :: l) r m1 m2 defm defmf)
  in  rec-m , rec-r , rec-l

-- rec - decreasing size
diamond (x1 :: m1) (x2 :: m2) (x3 :: m3) (cancel≅ (x :: l) r .(x1 :: m1) .(x2 :: m2) defm defmf) (cancel≅ (x₁ :: l₁) r₁ .(x1 :: m1) .(x3 :: m3) defm₁ defmf₁)  =
  let lemma = ≡-trans (≡-sym defm₁) defm
      rec-m , rec-l , rec-r = diamond m1 m2 m3 (cancel≅ l r m1 m2 (cut-head defm) (cut-head defmf))  (cancel≅ l₁ r₁ m1 m3 (cut-head defm₁) (cut-head defmf₁))
  in  _ , (l++ [ x2 ] rec-l , trans (idp≅* (head+tail (≡-trans (cut-tail defmf₁) (≡-trans (cut-tail lemma) (cut-tail (≡-sym defmf)))) idp)) (l++ [ x2 ] rec-r))
diamond (x1 :: m1) (x2 :: m2) (x3 :: m3) (cancel≅ (x₁ :: l) r .(x1 :: m1) .(x2 :: m2) defm defmf) (swap≅ p (x₂ :: l₁) r₁ .(x1 :: m1) .(x3 :: m3) defm₁ defmf₁) =
  let lemma = ≡-trans (≡-sym defm₁) defm
      rec-m , rec-l , rec-r = diamond m1 m2 m3 (cancel≅ l r m1 m2 (cut-head defm) (cut-head defmf))  (swap≅ p l₁ r₁ m1 m3 (cut-head defm₁) (cut-head defmf₁))
  in  _ , (l++ [ x2 ] rec-l , trans (idp≅* (head+tail (≡-trans (cut-tail defmf₁) (≡-trans (cut-tail lemma) (cut-tail (≡-sym defmf)))) idp)) (l++ [ x2 ] rec-r))
diamond (x1 :: m1) (x2 :: m2) (x3 :: m3) (swap≅ p (x₂ :: l) r .(x1 :: m1) .(x2 :: m2) defm defmf) (swap≅ p₁ (x₃ :: l₁) r₁ .(x1 :: m1) .(x3 :: m3) defm₁ defmf₁) =
  let lemma = ≡-trans (≡-sym defm₁) defm
      rec-m , rec-l , rec-r = diamond m1 m2 m3 (swap≅ p l r m1 m2 (cut-head defm) (cut-head defmf))  (swap≅ p₁ l₁ r₁ m1 m3 (cut-head defm₁) (cut-head defmf₁))
  in  _ , (l++ [ x2 ] rec-l , trans (idp≅* (head+tail (≡-trans (cut-tail defmf₁) (≡-trans (cut-tail lemma) (cut-tail (≡-sym defmf)))) idp)) (l++ [ x2 ] rec-r))
diamond (x1 :: m1) (x2 :: m2) (x3 :: m3) (cancel≅ (x :: l) r .(x1 :: m1) .(x2 :: m2) defm defmf)  (long≅ k (x₁ :: l₁) r₁ .(x1 :: m1) .(x3 :: m3) defm₁ defmf₁) =
  let lemma = ≡-trans (≡-sym defm₁) defm
      rec-m , rec-l , rec-r = diamond m1 m2 m3 (cancel≅ l r m1 m2 (cut-head defm) (cut-head defmf))  (long≅ k l₁ r₁ m1 m3 (cut-head defm₁) (cut-head defmf₁))
  in  _ , (l++ [ x2 ] rec-l , trans (idp≅* (head+tail (≡-trans (cut-tail defmf₁) (≡-trans (cut-tail lemma) (cut-tail (≡-sym defmf)))) idp)) (l++ [ x2 ] rec-r))
diamond (x1 :: m1) (x2 :: m2) (x3 :: m3) (swap≅ p (x₁ :: l) r .(x1 :: m1) .(x2 :: m2) defm defmf) (long≅ k (x₂ :: l₁) r₁ .(x1 :: m1) .(x3 :: m3) defm₁ defmf₁) =
  let lemma = ≡-trans (≡-sym defm₁) defm
      rec-m , rec-l , rec-r = diamond m1 m2 m3 (swap≅ p l r m1 m2 (cut-head defm) (cut-head defmf))  (long≅ k l₁ r₁ m1 m3 (cut-head defm₁) (cut-head defmf₁))
  in  _ , (l++ [ x2 ] rec-l , trans (idp≅* (head+tail (≡-trans (cut-tail defmf₁) (≡-trans (cut-tail lemma) (cut-tail (≡-sym defmf)))) idp)) (l++ [ x2 ] rec-r))
diamond (x1 :: m1) (x2 :: m2) (x3 :: m3) (long≅ k (x :: l) r .(x1 :: m1) .(x2 :: m2) defm defmf)  (long≅ k₁ (x₁ :: l₁) r₁ .(x1 :: m1) .(x3 :: m3) defm₁ defmf₁) =
  let lemma = ≡-trans (≡-sym defm₁) defm
      rec-m , rec-l , rec-r = diamond m1 m2 m3 (long≅ k l r m1 m2 (cut-head defm) (cut-head defmf))  (long≅ k₁ l₁ r₁ m1 m3 (cut-head defm₁) (cut-head defmf₁))
  in  _ , (l++ [ x2 ] rec-l , trans (idp≅* (head+tail (≡-trans (cut-tail defmf₁) (≡-trans (cut-tail lemma) (cut-tail (≡-sym defmf)))) idp)) (l++ [ x2 ] rec-r))

-- - abs
diamond .(_ :: _ :: r) m2 m3 (cancel≅ nil r .(_ :: _ :: r) .m2 idp defmf) (swap≅ x nil .r .(_ :: _ :: r) .m3 idp defmf₁) = abs-suc x

--- base cases when long is at the beginning
diamond m1 m2 m3 (cancel≅ {n₁} l r .m1 .m2 defm defmf) (long≅ {n} k nil r₁ .m1 .m3 defm₁ defmf₁)
  rewrite defmf rewrite defmf₁ =
  let eq = ≡-trans (≡-sym defm₁) defm
      rec-m , rec-r , rec-l = cancel-long-lemma n k n₁ r₁ l r eq
  in  rec-m , rec-l , rec-r
diamond m1 m2 m3 (swap≅ x l r .m1 .m2 defm defmf) (long≅ {n} k nil r₁ .m1 .m3 defm₁ defmf₁)
  rewrite defmf rewrite defmf₁ =
  let eq = ≡-trans (≡-sym defm₁) defm
      rec-m , rec-r , rec-l = swap-long-lemma n k _ _ x r₁ l r eq
  in  rec-m , rec-l , rec-r
diamond m1 m2 m3 (long≅ {n} k nil r .m1 .m2 defm defmf) (long≅ {n₁} k₁ l₁ r₁ .m1 .m3 defm₁ defmf₁)
  rewrite defmf rewrite defmf₁ =
  let eq = ≡-trans (≡-sym defm₁) defm
      rec-m , rec-l , rec-r = long-long-lemma n k n₁ k₁ r l₁ r₁ (≡-sym eq)
  in  rec-m , rec-l , rec-r

{-# NON_TERMINATING #-}
diamond-full : {m1 m2 m3 : List} -> (m1 ≅* m2) -> (m1 ≅* m3) -> Σ _ (λ m -> (m2 ≅* m) × (m3 ≅* m))
diamond-full idp q = _ , (q , idp)
diamond-full (trans≅ x p) idp = _ , idp , trans≅ x p
diamond-full (trans≅ x idp) (trans≅ y idp) = diamond _ _ _ x y
diamond-full {m1} {m2} {m3} (trans≅ x (trans≅ y p)) (trans≅ z idp) =
  let one-m , one-l , one-r = diamond _ _ _ x z
      rec-m , rec-l , rec-r = diamond-full {_} {m2} {one-m} (trans≅ y p) one-l
  in  rec-m , rec-l , trans one-r rec-r
diamond-full {m1} {m2} {m3} (trans≅ x p) (trans≅ y (trans≅ {m4} z q)) =
  let rec-m , rec-l , rec-r = diamond-full (trans≅ x p) (ext y)
      rec-mm , rec-ll , rec-rr = diamond-full {m4} {rec-m} {_} rec-r (trans≅ z q)
  in  rec-mm , trans rec-l rec-ll , rec-rr
