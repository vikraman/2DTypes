{-# OPTIONS --without-K --rewriting #-}

module Pi+.CoxeterNonParametrized.ExchangeLemmas+ where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.CoxeterCommon.Arithmetic
open import Pi+.CoxeterCommon.ListN
open import Pi+.CoxeterNonParametrized.ReductionRel
open import Pi+.CoxeterNonParametrized.ExchangeLemmas
open import Pi+.CoxeterNonParametrized.ReductionRel+

open ≅*-Reasoning

long-swap+ : (n1 n2 : ℕ) -> (k : ℕ) -> ((S k) + n1 < n2) -> (n2 :: (n1 ↓ (S k))) ≅+ ((n1 ↓ (S k)) ++ [ n2 ])
long-swap+ n1 n2 O p = trans≅+ (swap≅ p nil nil (n2 :: n1 :: nil) (n1 :: n2 :: nil) idp idp) idp
long-swap+ n1 n2 (S k) p =
  let rec = long-swap+ n1 n2 k (≤-down p)
  in  trans+ (swap+ p nil _) (+l++ [ S (k + n1) ] rec)

long-swap<+ : (n1 n2 : ℕ) -> (k : ℕ) -> (S n1 < n2) -> ((n2 ↓ (S k)) ++ [ n1 ]) ≅+ (n1 :: (n2 ↓ (S k)))
long-swap<+ n1 n2 O p = trans≅+ (swap≅ p nil nil (n2 :: n1 :: nil) (n1 :: n2 :: nil) idp idp) idp
long-swap<+ n1 n2 (S k) p =
  let rec = long-swap<+ n1 n2 k p
  in  trans+ (+l++ ((S k) + n2 :: nil) rec) (swap+ (≤-up-+ p) nil _)

long-swap-lr+ : (n1 n2 k : ℕ) -> (l r : Listℕ) -> ((S k) + n1 < n2) -> (l ++ (n2 :: (n1 ↓ (S k))) ++ r) ≅+ (l ++ (n1 ↓ (S k)) ++ n2 :: r)
long-swap-lr+ n1 n2 k l r p =
  let lemma = (++r+ r (long-swap+ n1 n2 k p))
  in  +l++ l (trans+* lemma (idp≅* (++-assoc (k + n1 :: n1 ↓ k) (n2 :: nil) r)))

long-swap<-lr+ : (n1 n2 k : ℕ) -> (l r : Listℕ) -> (S n1 < n2) -> (l ++ (n2 ↓ (S k)) ++ n1 :: r) ≅+ (l ++ n1 :: (n2 ↓ (S k)) ++ r)
long-swap<-lr+ n1 n2 k l r p =
  let lemma = (++r+ r (long-swap<+ n1 n2 k p))
  in  +l++ l (trans*+ (idp≅* (≡-sym (++-assoc (n2 ↓ (S k)) (n1 :: nil) r))) lemma)

short-swap+ : {n k t tl tr : ℕ} -> (tr + n == t) -> ((tl + S t) == S (k + n)) -> (n ↓ (2 + k) ++ [ S t ]) ≅+ (t :: (n ↓ (2 + k)))
short-swap+ {n} {k} {t} {tl} {tr} ptn ptkn rewrite (≡-sym ptn) =
  let pp = ≡-down-r-+ {r = n} (≡-trans (+-assoc tl (1 + tr) n) (≡-trans ptkn (≡-sym (+-assoc 1 k n))))
      k=tl+tr : 2 + k == tl + (2 + tr)
      k=tl+tr = ≡-trans (≡-sym (cong S pp)) (≡-sym (+-three-assoc {tl} {1} {1 + tr}))

      lemma : n ↓ (2 + k) == (n + (2 + tr)) ↓ tl ++ (n ↓ (2 + tr))
      lemma = ≡-trans (cong (λ e -> n ↓ e) k=tl+tr) (↓-+ n tl (2 + tr))

      red1 = 
        ≅*begin
          S (k + n) :: k + n :: (n ↓ k) ++ S (tr + n) :: nil
        ≅*⟨ idp≅* (start+end lemma idp) ⟩
          (((n + (2 + tr)) ↓ tl) ++ (n ↓ (2 + tr))) ++ S (tr + n) :: nil
        ≅*⟨ idp≅* (++-assoc ((n + S (S tr)) ↓ tl) _ (S (tr + n) :: nil) ) ⟩
          ((n + (2 + tr)) ↓ tl) ++ (n ↓ (2 + tr)) ++ S (tr + n) :: nil
        ≅*∎
      
      red2 = trans+* 
        (long+ tr ((n + ((S (S O)) + tr)) ↓ tl) nil) 
        (long-swap<-lr (tr + n) (n + ((S (S O)) + tr)) tl nil (S (tr + n) :: tr + n :: (n ↓ tr) ++ nil) (≤-reflexive (≡-trans (≡-sym (+-assoc (S (S O)) tr n)) (+-comm (S (S tr)) n))))
        
      red3 =
        ≅*begin
          _
        ≅*⟨ idp≅* (start+end (idp {a = (tr + n) :: ((n + (2 + tr)) ↓ tl)}) (++-unit {(n ↓ (2 + tr))})) ⟩
          (tr + n) :: ((n + (2 + tr)) ↓ tl) ++ (n ↓ (2 + tr))
        ≅*⟨ idp≅* (head+tail idp (≡-sym (↓-+ n tl (2 + tr)))) ⟩
          tr + n :: (n ↓ (tl + S (S tr)))
        ≅*⟨ idp≅* (head+tail idp (cong (λ e -> n ↓ e) (≡-sym k=tl+tr))) ⟩
          tr + n :: S (k + n) :: k + n :: (n ↓ k)
        ≅*∎
  in trans+* (trans*+ red1 red2) red3

short-swap-l+ : {n k t : ℕ} -> (l : Listℕ) -> (n ≤ t) -> (S t ≤ S (k + n)) -> (l ++ n ↓ (2 + k) ++ [ S t ]) ≅+ (l ++ t :: (n ↓ (2 + k)))
short-swap-l+ {n} {k} {t} l pnt ptkn =
  let tr , tr-p = ≤-∃ n t pnt
      tl , tl-p = ≤-∃ (S t) (S k + n) ptkn
      lemma = (short-swap+ {n} {k} {t} {tl} {tr} tr-p tl-p)
  in  +l++ l lemma

short-swap-lr+ : {n k t : ℕ} -> (l r : Listℕ) -> (n ≤ t) -> (S t ≤ S (k + n)) -> ((l ++ n ↓ (2 + k)) ++ S t :: r) ≅+ ((l ++ t :: (n ↓ (2 + k))) ++ r)
short-swap-lr+ {n} {k} {t} l r pnt ptkn =
  let tr , tr-p = ≤-∃ n t pnt
      tl , tl-p = ≤-∃ (S t) (S k + n) ptkn
      lemma = ++r+ r (+l++ l (short-swap+ {n} {k} {t} {tl} {tr} tr-p tl-p))
  in  trans*+ (idp≅* (≡-sym (≡-trans (start+end (≡-sym (++-assoc l _ [ _ ])) (idp {a = r})) (++-assoc _ [ _ ] r)))) lemma

long->-long+ : (n k n1 k1 : ℕ) -> (k + n == S (k1 + n1)) -> (k1 < k) -> ((n ↓ (2 + k)) ++ ((1 + n1) ↓ (2 + k1))) ≅+ ((n1 ↓ (2 + k1)) ++ (n ↓ (2 + k)))
long->-long+ n 0 n1 k1 pp ()
long->-long+ n (S k) n1 0 pp pk rewrite (≡-sym pp)  =
  let r1 = 
        ≅*begin
          (n ↓ (3 + k)) ++ (2 + (k + n)) :: (1 + (k + n)) :: nil
        ≅*⟨ long (1 + k) nil [ _ ] ⟩
          (1 + (k + n)) :: (n ↓ (3 + k)) ++ (1 + (k + n)) :: nil
        ≅*∎
      r2 = short-swap-lr+ {n = n} {k = (1 + k)} [ _ ] nil (≤-up-+ (≤-reflexive idp)) (≤-up (≤-reflexive idp))
      r3 = 
          ≅*begin
            _
          ≅*⟨ idp≅* ++-unit ⟩
            _
          ≅*⟨ idp≅* (head+tail idp (head+tail (≡-down2 pp) idp)) ⟩
            _
          ≅*∎
  in  trans*+ r1 (trans+* r2 r3)
long->-long+ n (S k) n1 (S k1) pp pk =
  let rec = long->-long+ n k n1 k1 (≡-down2 pp) (≤-down2 pk)
      r1 = short-swap-lr+ {n = n} {k = (1 + k)} nil (((1 + n1) ↓ (2 + k1))) (≤-trans (≤-trans (≤-up (≤-up-+ rrr)) (≤-reflexive pp)) (≤-reflexive (≡-sym (+-three-assoc {1 + k1} {1} {_})))) (≤-reflexive (cong S (≡-trans (+-three-assoc {1 + k1} {1} {_}) (≡-sym pp))))
      r2 =
        ≅*begin
          _ :: _ :: (n ↓ (2 + k)) ++ ((1 + n1) ↓ (2 + k1))
        ≅*⟨ l++ (_ :: _ :: nil) (ext* rec) ⟩
          _ :: _ :: (n1 ↓ (2 + k1)) ++ (n ↓ (2 + k))
        ≅*⟨ long-swap-lr n1 (S (S (k + n))) (S (S k1)) [ _ ] ((n ↓ (2 + k))) (≤-reflexive (cong S (≡-sym pp))) ⟩
          _ :: (n1 ↓ (2 + k1)) ++ _ :: (n ↓ (2 + k))
        ≅*⟨ idp≅* (head+tail (+-three-assoc {1 + k1} {1} {n1}) idp) ⟩
          (n1 ↓ (3 + k1)) ++ (n ↓ (3 + k))
        ≅*∎
  in  trans+* r1 r2
-- long-≤-long : (n k n1 k1 : ℕ) -> (k + n == k1 + n1) -> (k ≤ k1) -> ((n ↓ (2 + k)) ++ (n1 ↓ (2 + k1))) ≅+ ((n1 ↓ (1 + k1)) ++ ((1 + n) ↓ (1 + k)))
-- long-≤-long n 0 n1 k1 pp pk rewrite pp rewrite (+-three-assoc {k1} {1} {n1}) =
--   ≅*begin
--     _
--   ≅*⟨ braid nil _ ⟩
--     _
--   ≅*⟨ cancel (_ :: _ :: nil)  _ ⟩
--     _
--   ≅*⟨ idp≅* (≡-sym (++-unit)) ⟩
--     _
--   ≅*⟨ long-swap-lr n1 (1 + k1 + n1) k1 [ _ ] nil (≤-reflexive idp) ⟩
--     _
--   ≅*∎
-- long-≤-long n (S k) n1 0 pp ()
-- long-≤-long n (S k) n1 (S k1) pp pk =
--   let rec = long-≤-long n k n1 k1 (≡-down2 pp) (≤-down2 pk)
--       lemma = (≡-sym (cong (λ e -> 2 + e) (≡-trans (+-three-assoc {k} {1} {n}) (≡-trans pp (≡-sym (+-three-assoc {k1} {1} {n1}))))))
--   in
--     ≅*begin
--       (n ↓ (3 + k)) ++ 2 + k1 + n1 :: (n1 ↓ (2 + k1))
--     ≅*⟨ short-swap-lr {n = n} nil ((n1 ↓ (2 + k1))) (≤-trans (≤-up (≤-up-+ (≤-reflexive idp))) (≤-reflexive pp)) (s≤s (≤-reflexive (≡-sym pp))) ⟩
--        1 + k1 + n1 :: (2 + k + n) :: (n ↓ (2 + k)) ++ (n1 ↓ (2 + k1))
--     ≅*⟨ idp≅* (++-assoc (_ :: _ :: nil) ((n ↓ (2 + k))) _) ⟩
--       1 + k1 + n1 :: (2 + k + n) :: nil ++ (((n ↓ (2 + k)) ++ (n1 ↓ (2 + k1))))
--     ≅*⟨ l++ (_ :: _ :: nil) rec ⟩
--       1 + k1 + n1 :: (2 + k + n) :: nil ++ (((n1 ↓ (1 + k1)) ++ ((1 + n) ↓ (1 + k))))
--     ≅*⟨ idp≅* (≡-sym (++-assoc (_ :: _ :: nil) (n1 ↓ (1 + k1)) _)) ⟩
--       _
--     ≅*⟨ long-swap-lr n1 (S (S (k + n))) (S k1) [ _ ] ((1 + n) ↓ (1 + k)) (≤-reflexive (cong S (≡-sym pp))) ⟩
--       1 + k1 + n1 :: (n1 ↓ (1 + k1)) ++ (2 + k + n) :: ((1 + n) ↓ (1 + k))
--     ≅*⟨ idp≅* (start+end (idp {a = 1 + k1 + n1 :: (n1 ↓ (1 + k1))})  (head+tail (≡-sym (+-three-assoc {1 + k} {1} {n})) idp)) ⟩
--       _
--     ≅*∎