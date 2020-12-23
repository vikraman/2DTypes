{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.CritPairsLong where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.Coxeter.Arithmetic
open import Pi+.Coxeter.Lists
open import Pi+.Coxeter.ReductionRel
open import Pi+.Coxeter.CritPairsSwap
open import Pi+.Coxeter.CritPairsImpossible

open ≅*-Reasoning

long-lemma : (n n1 k k1 t t1 : ℕ) -> (S n ≤ t) -> (S n1 ≤ t1) -> (r r1 : List) -> (n ↓ (2 + k)) ++ t :: r == (n1 ↓ (2 + k1)) ++ t1 :: r1
             -> (n == n1) × ((n ↓ (2 + k)) == (n1 ↓ (2 + k1))) × (r == r1)
long-lemma n n1 0 0 t t1 pnt pnt1 r r1 p rewrite (cut-t1 p) rewrite (cut-t2 p) rewrite (cut-t3 p) rewrite (cut-h3 p) = idp , (idp , idp)
long-lemma n n1 0 (S k1) t t1 pnt pnt1 r r1 p rewrite (cut-t1 p) rewrite (cut-t2 p) rewrite (cut-t3 p) rewrite (cut-h3 p) = abs-suc pnt
long-lemma n n1 (S k) 0 t t1 pnt pnt1 r r1 p rewrite ≡-sym (cut-t1 p) rewrite ≡-sym (cut-t2 p) rewrite ≡-sym (cut-t3 p) rewrite (cut-h3 p) = abs-suc pnt1
long-lemma n n1 (S k) (S k1) t t1 pnt pnt1 r r1 p =
  let rec-m , rec-l , rec-r = long-lemma n n1 k k1 t t1 pnt pnt1 r r1 (cut-head p)
  in  rec-m , ((head+tail (cong S (cut-t2 p) ) rec-l) , rec-r)

cancel-long-lemma-rev : (n k n1 : ℕ) -> (r l1 r1 : List) -> ((r ++ (1 + k + n) :: (n ↑ (2 + k))) == (r1 ++ n1 :: n1 :: l1)) -> Σ _ (λ mf -> (((((k + n) :: (n ↓ (2 + k)) ++ (rev r)) ≅* mf)) × ((((rev l1) ++ (rev r1))) ≅* mf)))
cancel-long-lemma-rev n k n1 nil l1 nil p =
  let fst = cut-t1 p
      snd = cut-t2 p
  in  abs-refl (≤-trans (≤-reflexive fst) (≤-trans (≤-reflexive (≡-sym snd)) (≤-up-+ rrr)))
cancel-long-lemma-rev n 0 n1 nil l1 (x :: x₁ :: nil) ()
cancel-long-lemma-rev n (S k) n1 nil l1 (x :: x₁ :: nil) ()
cancel-long-lemma-rev n k n1 nil l1 (x :: x₁ :: x₂ :: r1) p =
  let cut = cut-h3 p
  in  ⊥-elim (repeat-long-lemma-rev (S (S n)) k n1 r1 l1 (cut-h3 p))
cancel-long-lemma-rev n k .(S (k + n)) (.(S (k + n)) :: nil) .(n :: S n :: (S (S n) ↑ k)) nil idp =
  let left =
        ≅*begin
          k + n :: S (k + n) :: k + n :: (n ↓ k) ++ S (k + n) :: nil
        ≅*⟨ long k [ k + n ] nil ⟩
          k + n :: k + n :: S (k + n) :: k + n :: (n ↓ k) ++ nil
        ≅*⟨ cancel nil _ ⟩
          S (k + n) :: k + n :: (n ↓ k) ++ nil
        ≅*⟨ idp≅* (++-unit) ⟩
          (n ↓ (2 + k))
        ≅*∎
      right =
        begin
          ((rev (S (S n) ↑ k) ++ S n :: nil) ++ n :: nil) ++ nil
        =⟨ ++-unit ⟩
          (rev (S (S n) ↑ k) ++ S n :: nil) ++ n :: nil
        =⟨ start+end (start+end (rev-u (2 + n) k) idp) idp ⟩
          ((S (S n) ↓ k) ++ S n :: nil) ++ n :: nil
        =⟨ start+end (++-↓ (1 + n) k) idp ⟩
          k + S n :: (S n ↓ k) ++ n :: nil
        =⟨ ++-↓ n (1 + k) ⟩
          S (k + n) :: k + n :: (n ↓ k)
        =∎
  in  _ , ( left , idp≅* right)

cancel-long-lemma-rev n k n1 (.n1 :: .n1 :: r) .(r ++ S (k + n) :: n :: S n :: (S (S n) ↑ k)) nil idp =
  let left =
        ≅*begin
          (rev r ++ n1 :: nil) ++ n1 :: nil
        ≅*⟨ idp≅* (++-assoc (rev r) [ n1 ] (n1 :: nil)) ⟩
          rev r ++ n1 :: n1 :: nil
        ≅*⟨ (cancel (rev r) nil) ⟩
          rev r ++ nil
        ≅*⟨ (idp≅* ++-unit) ⟩
          rev r
        ≅*∎
      right =
        begin
          rev (r ++ S (k + n) :: n :: S n :: (S (S n) ↑ k)) ++ nil
        =⟨ ++-unit ⟩
          rev (r ++ S (k + n) :: n :: S n :: (S (S n) ↑ k))
        =⟨ rev-++ r (S (k + n) :: n :: S n :: (S (S n) ↑ k)) ⟩
          (((rev (S (S n) ↑ k) ++ S n :: nil) ++ n :: nil) ++ S (k + n) :: nil) ++ rev r
        =⟨ start+end (start+end (start+end (start+end (rev-u (2 + n) k) idp) idp) idp) idp ⟩
          ((((S (S n) ↓ k) ++ S n :: nil) ++ n :: nil) ++ S (k + n) :: nil) ++ rev r
        =⟨ start+end (start+end (start+end (++-↓ (1 + n) k) idp) idp) idp ⟩
          k + S n :: (((S n ↓ k) ++ n :: nil) ++ S (k + n) :: nil) ++ rev r
        =⟨ start+end (start+end (++-↓ n (1 + k)) idp) idp ⟩
          S (k + n) :: k + n :: ((n ↓ k) ++ S (k + n) :: nil) ++ rev r
        =∎
      right* =
        ≅*begin
          rev (r ++ S (k + n) :: n :: S n :: (S (S n) ↑ k)) ++ nil
        ≅*⟨ idp≅* right ⟩
          S (k + n) :: k + n :: ((n ↓ k) ++ S (k + n) :: nil) ++ rev r
        ≅*⟨ ++r (rev r) (long k nil nil) ⟩
          k + n :: S (k + n) :: k + n :: ((n ↓ k) ++ nil) ++ rev r
        ≅*⟨ ++r (rev r) (l++ (k + n :: S (k + n) :: k + n :: nil) (idp≅* ++-unit)) ⟩
          k + n :: S (k + n) :: k + n :: (n ↓ k) ++ rev r
        ≅*∎
  in  _ , ( l++ (k + n :: S (k + n) :: k + n :: (n ↓ k)) left , right* )
cancel-long-lemma-rev n k n1 (x :: r) l1 (x₁ :: r1) p rewrite (≡-sym (cut-tail p)) =
  let rec-m , rec-l , rec-r = cancel-long-lemma-rev n k n1 r l1 r1 (cut-head p)
      ll = trans (idp≅* (≡-sym (++-assoc (k + n :: S (k + n) :: k + n :: (n ↓ k)) (rev r) [ x ]))) (++r [ x ] rec-l)
      rr = trans (idp≅* (≡-sym (++-assoc (rev l1) (rev r1) [ x ]))) (++r [ x ] rec-r)
  in  _ , (ll , rr)

cancel-long-lemma : (n k n1 : ℕ) -> (r l1 r1 : List) -> (((n ↓ (2 + k)) ++ (1 + k + n) :: r) == (l1 ++ n1 :: n1 :: r1)) -> Σ _ (λ mf -> (((((k + n) :: (n ↓ (2 + k)) ++ r) ≅* mf)) × (((l1 ++ r1)) ≅* mf)))
cancel-long-lemma n k n1 r l1 r1 p =
  let pp =
        begin
          rev r ++ S (k + n) :: n :: S n :: (S (S n) ↑ k)
        =⟨ start+end idp (start+end (idp {a = [ S (k + n) ]}) (≡-sym (++-↑ n (S k)))) ⟩
          rev r ++ S (k + n) :: n :: (S n ↑ k) ++ S (k + n) :: nil
        =⟨ start+end idp (start+end (idp {a = [ S (k + n) ]}) (≡-sym (start+end (++-↑ n k) idp))) ⟩
          rev r ++ S (k + n) :: nil ++ ((n ↑ k) ++ [ k + n ] ) ++ S (k + n) :: nil
        =⟨ start+end (idp {a = rev r}) (start+end (idp {a = [ S (k + n) ]}) (++-assoc (n ↑ k) (k + n :: nil) (S (k + n) :: nil))) ⟩
          rev r ++ S (k + n) :: nil ++ (n ↑ k) ++ k + n :: S (k + n) :: nil
        =⟨ start+end idp (start+end (idp {a = [ S (k + n) ]}) (start+end (≡-sym (rev-d n k)) idp)) ⟩
          rev r ++ S (k + n) :: nil ++ rev (n ↓ k) ++ k + n :: S (k + n) :: nil
        =⟨ ≡-sym (++-assoc (rev r) (S (k + n) :: nil) (rev (n ↓ k) ++ k + n :: S (k + n) :: nil)) ⟩
          (rev r ++ S (k + n) :: nil) ++ rev (n ↓ k) ++ k + n :: S (k + n) :: nil
        =⟨ ≡-sym (++-assoc _ (rev (n ↓ k)) (k + n :: S (k + n) :: nil)) ⟩
          ((rev r ++ S (k + n) :: nil) ++ rev (n ↓ k)) ++ k + n :: S (k + n) :: nil
        =⟨ ≡-sym (start+end (rev-++ (n ↓ k) (S (k + n) :: r)) idp) ⟩
          rev ((n ↓ k) ++ S (k + n) :: r) ++ k + n :: S (k + n) :: nil
        =⟨ ≡-sym (++-assoc (rev ((n ↓ k) ++ S (k + n) :: r)) (k + n :: nil) (S (k + n) :: nil))  ⟩
          (rev ((n ↓ k) ++ S (k + n) :: r) ++ k + n :: nil) ++ S (k + n) :: nil
        =⟨ cong rev p ⟩
          rev (l1 ++ n1 :: n1 :: r1)
        =⟨ rev-++ l1 (n1 :: n1 :: r1) ⟩
          ((rev r1 ++ n1 :: nil) ++ n1 :: nil) ++ rev l1
        =⟨ ++-assoc (rev r1 ++ n1 :: nil) (n1 :: nil) (rev l1) ⟩
          (rev r1 ++ n1 :: nil) ++ n1 :: rev l1
        =⟨ ++-assoc _ [ n1 ] _ ⟩
          rev r1 ++ n1 :: n1 :: rev l1
        =∎
      call-m , call-l , call-r = cancel-long-lemma-rev n k n1 (rev r) (rev l1) (rev r1) pp
      ll = trans (idp≅* (start+end idp (rev-rev {r}))) call-l
      rr = trans (idp≅* (start+end (rev-rev {l1}) (start+end idp (rev-rev {r1})))) call-r
  in  call-m , ll , rr

swap-long-lemma-base : (n k k1 : ℕ) -> (pkn : S k1 < S (k + n))
                       -> (q1 : k1 ≤ n) -> (q2 : n ≤ 1 + k1)
                       -> ((k1 :: (1 + k + n) :: (n ↑ (2 + k))) == (k1 :: S (k + n) :: (n ↑ (2 + k))))
                       -> Σ _ (λ mf -> (((k + n) :: (n ↓ (2 + k)) ++ [ k1 ]) ≅* mf) × (((rev (n ↑ (2 + k))) ++ (k1 :: S (k + n) :: nil)) ≅* mf))
swap-long-lemma-base n k k1 pkn q1 q2 p with (≤-∃ _ _ q1)
swap-long-lemma-base n 0 k1 pkn q1 q2 p | 0 , snd rewrite (≡-sym snd) = abs-refl pkn
swap-long-lemma-base n (S k) k1 pkn q1 q2 p | 0 , snd rewrite (≡-sym snd) =
  let left = idp≅* (head+tail (≡-sym (+-three-assoc {k} {1} {k1}))
                   (head+tail (≡-sym (+-three-assoc {1 + k} {1} {k1}))
                   (head+tail (≡-sym (+-three-assoc {k} {1} {k1})) idp)))
      left* =
        ≅*begin
          _
        ≅*⟨ left ⟩
          k + S k1 :: S (k + S k1) :: k + S k1 :: (k1 ↓ (1 + k)) ++ k1 :: nil
        ≅*⟨ idp≅* (start+end (idp {a = k + S k1 :: S (k + S k1) :: k + S k1 :: nil}) (start+end (≡-sym (++-↓ k1 k)) idp)) ⟩
          k + S k1 :: S (k + S k1) :: k + S k1 :: ((S k1 ↓ k) ++ k1 :: nil) ++ k1 :: nil
        ≅*⟨ idp≅* (++-assoc (k + S k1 ::  S (k + S k1) :: k + S k1 :: (S k1 ↓ k)) [ k1 ] [ k1 ]) ⟩
          k + S k1 ::  S (k + S k1) :: k + S k1 :: (S k1 ↓ k) ++ k1 :: k1 :: nil
        ≅*⟨ cancel _ nil ⟩
          k + S k1 :: S (k + S k1) :: k + S k1 :: (S k1 ↓ k) ++ nil
        ≅*⟨ idp≅* ++-unit ⟩
          k + S k1 :: S (k + S k1) :: k + S k1 :: (S k1 ↓ k)
        ≅*∎
      right =
        ≅*begin
          _
        ≅*⟨ idp≅* (++-assoc _ (k1 :: nil) (k1 :: S (S (k + k1)) :: nil)) ⟩
          _
        ≅*⟨ idp≅* (telescope-rev (S k1) k (k1 :: k1 :: S (S (k + k1)) :: nil)) ⟩
          _
        ≅*⟨ cancel ((1 + k1) ↓ (2 + k)) (S (S (k + k1)) :: nil) ⟩
          _
        ≅*⟨ l++ (S k1 ↓ (2 + k)) (idp≅* (head+tail (≡-sym (+-three-assoc {1 + k} {1} {k1})) idp)) ⟩
          (S k1 ↓ (2 + k)) ++ S (k + S k1) :: nil
        ≅*⟨ long {1 + k1} k nil nil ⟩
          k + S k1 :: (S k1 ↓ (2 + k)) ++ nil
        ≅*⟨ idp≅* ++-unit ⟩
          k + S k1 :: (S k1 ↓ (2 + k))
        ≅*∎
  in  _  , (left* , right)
swap-long-lemma-base n k k1 pkn q1 q2 p | S 0 , snd rewrite (≡-sym snd) =
  let left = l++ (k + S k1 :: S (k + S k1) :: nil) (idp≅* (++-↓ k1 (1 + k) ))
      right =
        ≅*begin
          _
        ≅*⟨ idp≅* (telescope-rev (S k1) k (k1 :: (S (k + S k1)) :: nil)) ⟩
          (S k1 ↓ (2 + k)) ++ k1 :: S (k + S k1) :: nil
        ≅*⟨ idp≅* (≡-sym (++-assoc (S k1 ↓ (2 + k)) _ (S (k + S k1) :: nil))) ⟩
          ((S k1 ↓ (2 + k)) ++ k1 :: nil) ++ S (k + S k1) :: nil
        ≅*⟨ ++r (S (k + S k1) :: nil) (idp≅* (++-↓ k1 ( 2 + k )))   ⟩
          (k1 ↓ (3 + k)) ++ S (k + S k1) :: nil
        ≅*⟨ short-swap-l {k1} {S k} {k + S k1} nil (≤-trans (≤-up rrr) (≤-up-+ rrr)) (s≤s (≤-reflexive (+-three-assoc {k} {1} {k1}))) ⟩
          k + S k1 :: S (S (k + k1)) :: S (k + k1) :: k + k1 :: (k1 ↓ k)
        ≅*⟨ idp≅* (head+tail idp (head+tail (≡-sym (+-three-assoc {1 + k} {1} {k1})) idp)) ⟩
          k + S k1 :: S (k + S k1) :: (k1 ↓ (2 + k))
        ≅*∎
  in  _ , (left , right)
swap-long-lemma-base n k k1 pkn q1 q2 p | S (S fst) , snd rewrite (≡-sym snd) = abs-refl (≤-trans q2 (s≤s (≤-up-+ rrr)))

swap-long-lemma-rev : (n k n1 k1 : ℕ) -> (pkn : S k1 < n1)-> (r l1 r1 : List) -> ((r ++ (1 + k + n) :: (n ↑ (2 + k))) == (r1 ++ k1 :: n1 :: l1)) -> Σ _ (λ mf -> (((((k + n) :: (n ↓ (2 + k)) ++ (rev r)) ≅* mf)) × ((((rev l1) ++ (k1 :: n1 :: rev r1))) ≅* mf)))
swap-long-lemma-rev n k n1 k1 pkn nil l1 nil p =
  let fst = cut-t1 p
      snd = cut-t2 p
  in  abs-refl (≤-trans (≤-trans (≤-trans (s≤s (≤-up (≤-up (≤-up-+ rrr)))) (≤-reflexive (cong (λ e -> 2 + e ) fst))) pkn) (≤-reflexive (≡-sym snd)))
swap-long-lemma-rev n k .(S n) .n pkn nil .(S (S n) ↑ k) (.(S (k + n)) :: nil) idp = abs-refl pkn
swap-long-lemma-rev n (S k) .(S (S n)) .(S n) pkn nil .(S (S (S n)) ↑ k) (.(S (S (k + n))) :: .n :: nil) idp = abs-refl pkn
swap-long-lemma-rev n k n1 k1 pkn nil l1 (x :: x₁ :: x₂ :: r1) p = ⊥-elim (incr-long-lemma-rev (S (S n)) k n1 k1 pkn r1 l1 (cut-h3 p))

swap-long-lemma-rev n k .(S (k + n)) k1 pkn (.k1 :: nil) .(n :: S n :: (S (S n) ↑ k)) nil idp with S k1 <? n
... | yes p =
  let left =
        ≅*begin
          k + n :: S (k + n) :: k + n :: (n ↓ k) ++ k1 :: nil
        ≅*⟨ long-swap<-lr k1 n (2 + k) [ k + n ] nil p ⟩
          k + n :: k1 :: S (k + n) :: k + n :: (n ↓ k) ++ nil
        ≅*⟨ idp≅* (++-unit) ⟩
          k + n :: k1 :: S (k + n) :: k + n :: (n ↓ k)
        ≅*⟨ swap (≤-trans p (≤-up-+ rrr)) nil _ ⟩
          k1 :: k + n :: S (k + n) :: k + n :: (n ↓ k)
        ≅*∎
      right = telescope-rev n k (k1 :: S (k + n) :: nil)
      right* =
        ≅*begin
          ((rev (S (S n) ↑ k) ++ S n :: nil) ++ n :: nil) ++ k1 :: S (k + n) :: nil
        ≅*⟨ idp≅* right ⟩
          S (k + n) :: k + n :: (n ↓ k) ++ k1 :: S (k + n) :: nil
        ≅*⟨ long-swap<-lr k1 n (S (S k)) nil (S (k + n) :: nil) p ⟩
          k1 :: S (k + n) :: k + n :: (n ↓ k) ++ S (k + n) :: nil
        ≅*⟨ long k [ k1 ] nil ⟩
          k1 :: k + n :: S (k + n) :: k + n :: (n ↓ k) ++ nil
        ≅*⟨ idp≅* (++-unit) ⟩
          k1 :: k + n :: S (k + n) :: k + n :: (n ↓ k)
        ≅*∎
  in  _ , ( left , right*)
swap-long-lemma-rev n k .(S (k + n)) k1 pkn (.k1 :: nil) .(n :: (S n ↑ S k)) nil idp | no q with n <? k1
... | no q2 =
  let qq = ≰⇒> q
      qq2 = ≰⇒> q2
  in  swap-long-lemma-base n k k1 pkn (≤-down2 qq2) (≤-down2 qq) idp
... | yes q2 =
  let sk1 , sk1p = ≤-∃ 1 k1 (≤-down-+ q2)
      qq : n < 2 + k1
      qq = ≰⇒> q

      k1=1+sk1 : k1 == S sk1
      k1=1+sk1 = ≡-trans (≡-sym sk1p) (+-comm _ 1)

      n≤sk1 : n ≤ sk1
      n≤sk1 = (≤-down2 (≤-trans q2 (≤-reflexive k1=1+sk1)))
      sk1≤k+n : S sk1 ≤ S (k + n)
      sk1≤k+n = (≤-trans (s≤s (≤-up (≤-down (≤-reflexive (≡-sym k1=1+sk1))))) pkn)
      left =
        ≅*begin
          k + n :: (n ↓ (2 + k)) ++ k1 :: nil
        ≅*⟨ idp≅* (cong (λ e -> (k + n :: S (k + n) :: k + n :: (n ↓ k)) ++ [ e ]) k1=1+sk1) ⟩
          k + n :: (n ↓ (2 + k)) ++ (S sk1) :: nil
        ≅*⟨ short-swap-l [ k + n ] n≤sk1 sk1≤k+n ⟩
          k + n :: sk1 :: (n ↓ (2 + k))
        ≅*⟨ swap (≤-down2 (≤-trans (s≤s (s≤s (≤-reflexive (≡-sym k1=1+sk1)))) pkn)) nil _ ⟩
          sk1 :: k + n :: (n ↓ (2 + k))
        ≅*∎
      right = telescope-rev n k ((S sk1) :: S (k + n) :: nil)
      right* =
        ≅*begin
          _
        ≅*⟨ idp≅* (cong (λ e -> ((rev (S (S n) ↑ k) ++ S n :: nil) ++ n :: nil) ++ e :: S (k + n) :: nil ) k1=1+sk1) ⟩
          ((rev (S (S n) ↑ k) ++ S n :: nil) ++ n :: nil) ++ (S sk1) :: S (k + n) :: nil
        ≅*⟨ idp≅* right ⟩
           (n ↓ (2 + k)) ++ (S sk1) :: S (k + n) :: nil
        ≅*⟨ idp≅* (≡-sym (++-assoc (n ↓ (2 + k)) [ S sk1 ] [ S (k + n) ])) ⟩
          ((n ↓ (2 + k)) ++ [ S sk1 ]) ++ S (k + n) :: nil
        ≅*⟨ ++r [ S (k + n) ] (short-swap-l nil n≤sk1 sk1≤k+n) ⟩
          sk1 :: (n ↓ (2 + k)) ++ S (k + n) :: nil
        ≅*⟨ short-swap-l [ sk1 ] (≤-up-+ rrr) rrr ⟩
          _
        ≅*∎
  in  _ , (left , right*)
swap-long-lemma-rev n k n1 k1 pkn (.k1 :: .n1 :: r) .(r ++ S (k + n) :: n :: S n :: (S (S n) ↑ k)) nil idp =
  let left =
        ≅*begin
          (rev r ++ n1 :: nil) ++ k1 :: nil
        ≅*⟨ idp≅* (++-assoc (rev r) [ n1 ] [ k1 ]) ⟩
          rev r ++ n1 :: nil ++ k1 :: nil
        ≅*⟨ swap pkn (rev r) nil ⟩
          rev r ++ k1 :: nil ++ n1 :: nil
        ≅*∎
      right =
        ≅*begin
          rev (r ++ S (k + n) :: n :: S n :: (S (S n) ↑ k))
        ≅*⟨ idp≅* (rev-++ r _) ⟩
          (((rev (S (S n) ↑ k) ++ S n :: nil) ++ n :: nil) ++ S (k + n) :: nil) ++ rev r
        ≅*⟨ ++r (rev r) (idp≅* (start+end (start+end (start+end (rev-u (2 + n) k) idp) idp) idp)) ⟩
          ((((S (S n) ↓ k) ++ S n :: nil) ++ n :: nil) ++ S (k + n) :: nil) ++ rev r
        ≅*⟨ ++r (rev r) (idp≅* (start+end (start+end (++-↓ (1 + n) k) idp) idp)) ⟩
          k + S n :: (((S n ↓ k) ++ n :: nil) ++ S (k + n) :: nil) ++ rev r
        ≅*⟨ ++r (rev r) (idp≅* (start+end (++-↓ n (1 + k)) idp)) ⟩
          S (k + n) :: k + n :: ((n ↓ k) ++ S (k + n) :: nil) ++ rev r
        ≅*⟨ ++r (rev r) (long k nil nil) ⟩
          k + n :: S (k + n) :: k + n :: ((n ↓ k) ++ nil) ++ rev r
        ≅*⟨ ++r (rev r) (l++ (k + n :: S (k + n) :: k + n :: nil) (idp≅* (++-unit))) ⟩
          k + n :: S (k + n) :: k + n :: (n ↓ k) ++ rev r
        ≅*∎
      right* =
        ≅*begin
          rev (r ++ S (k + n) :: n :: S n :: (S (S n) ↑ k)) ++ k1 :: n1 :: nil
        ≅*⟨ ++r (k1 :: n1 :: nil) right ⟩
          k + n :: S (k + n) :: k + n :: ((n ↓ k) ++ rev r) ++ k1 :: n1 :: nil
        ≅*⟨ idp≅* (++-assoc (k + n :: S (k + n) :: k + n :: (n ↓ k)) (rev r) (k1 :: n1 :: nil)) ⟩
          k + n :: S (k + n) :: k + n :: (n ↓ k) ++ rev r ++ k1 :: n1 :: nil
        ≅*∎
  in  _ , ( (l++ (k + n :: S (k + n) :: k + n :: (n ↓ k)) left) , right*)
swap-long-lemma-rev n k n1 k1 pkn (x :: r) l1 (x₁ :: r1) p rewrite (≡-sym (cut-tail p)) =
  let rec-m , rec-l , rec-r = swap-long-lemma-rev n k n1 k1 pkn r l1 r1 (cut-head p)
      ll = trans (idp≅* (≡-sym (++-assoc (k + n :: S (k + n) :: k + n :: (n ↓ k)) (rev r) [ x ]))) (++r [ x ] rec-l)
      rr = trans (idp≅* (≡-sym (++-assoc (rev l1) ( _ :: _ :: rev r1) [ x ]))) (++r [ x ] rec-r)
  in  _ , (ll , rr)


swap-long-lemma : (n k n1 k1 : ℕ) -> (pkn : S k1 < n1) -> (r l1 r1 : List) -> (((n ↓ (2 + k)) ++ (1 + k + n) :: r) == (l1 ++ n1 :: k1 :: r1)) -> Σ _ (λ mf -> (((((k + n) :: (n ↓ (2 + k)) ++ r) ≅* mf)) × (((l1 ++ (k1 :: n1 :: r1))) ≅* mf)))
swap-long-lemma n k n1 k1 pkn r l1 r1 p =
  let pp =
        begin
          rev r ++ S (k + n) :: n :: S n :: (S (S n) ↑ k)
        =⟨ start+end idp (start+end (idp {a = [ S (k + n) ]}) (≡-sym (++-↑ n (S k)))) ⟩
          rev r ++ S (k + n) :: n :: (S n ↑ k) ++ S (k + n) :: nil
        =⟨ start+end idp (start+end (idp {a = [ S (k + n) ]}) (≡-sym (start+end (++-↑ n k) idp))) ⟩
          rev r ++ S (k + n) :: nil ++ ((n ↑ k) ++ [ k + n ] ) ++ S (k + n) :: nil
        =⟨ start+end (idp {a = rev r}) (start+end (idp {a = [ S (k + n) ]}) (++-assoc (n ↑ k) (k + n :: nil) (S (k + n) :: nil))) ⟩
          rev r ++ S (k + n) :: nil ++ (n ↑ k) ++ k + n :: S (k + n) :: nil
        =⟨ start+end idp (start+end (idp {a = [ S (k + n) ]}) (start+end (≡-sym (rev-d n k)) idp)) ⟩
          rev r ++ S (k + n) :: nil ++ rev (n ↓ k) ++ k + n :: S (k + n) :: nil
        =⟨ ≡-sym (++-assoc (rev r) (S (k + n) :: nil) (rev (n ↓ k) ++ k + n :: S (k + n) :: nil)) ⟩
          (rev r ++ S (k + n) :: nil) ++ rev (n ↓ k) ++ k + n :: S (k + n) :: nil
        =⟨ ≡-sym (++-assoc _ (rev (n ↓ k)) (k + n :: S (k + n) :: nil)) ⟩
          ((rev r ++ S (k + n) :: nil) ++ rev (n ↓ k)) ++ k + n :: S (k + n) :: nil
        =⟨ ≡-sym (start+end (rev-++ (n ↓ k) (S (k + n) :: r)) idp) ⟩
          rev ((n ↓ k) ++ S (k + n) :: r) ++ k + n :: S (k + n) :: nil
        =⟨ ≡-sym (++-assoc (rev ((n ↓ k) ++ S (k + n) :: r)) (k + n :: nil) (S (k + n) :: nil))  ⟩
          (rev ((n ↓ k) ++ S (k + n) :: r) ++ k + n :: nil) ++ S (k + n) :: nil
        =⟨ cong rev p ⟩
          rev (l1 ++ n1 :: k1 :: r1)
        =⟨ rev-++ l1 (n1 :: k1 :: r1) ⟩
          ((rev r1 ++ k1 :: nil) ++ n1 :: nil) ++ rev l1
        =⟨ ++-assoc (rev r1 ++ k1 :: nil) (n1 :: nil) (rev l1) ⟩
          (rev r1 ++ k1 :: nil) ++ n1 :: rev l1
        =⟨ ++-assoc _ [ k1 ] _ ⟩
          rev r1 ++ k1 :: n1 :: rev l1
        =∎
      call-m , call-l , call-r = swap-long-lemma-rev n k n1 k1 pkn (rev r) (rev l1) (rev r1) pp
      ll = trans (idp≅* (start+end idp (rev-rev {r}))) call-l
      rr = trans (idp≅* (start+end (rev-rev {l1}) (start+end idp (rev-rev {r1})))) call-r
  in  call-m , ll , rr


ar-lemma : (k1 k2 : ℕ) -> {n1 n2 : ℕ} -> (n1 == n2) -> S (k1 + n1) == S (k2 + n2) -> k1 == k2
ar-lemma k1 k2 pn p rewrite pn = ≡-down-r-+ (≡-down2 p)

dec-long-lemma-disjoint-rev : (n k n1 k1 x : ℕ) -> (n < x) -> (l r : List) -> l ++ x :: (n ↑ (1 + k)) == (n1 ↑ (1 + k1)) ++ r
                              -> ((l == (n1 ↑ k1)) × (x == n1 + k1) × (r == (n ↑ (1 + k)))) ⊎
                                  Σ (List) (λ m -> (l == (n1 ↑ (1 + k1)) ++ m) × (r == m ++ x :: (n ↑ (1 + k))))
dec-long-lemma-disjoint-rev n k n1 0 .n1 pnx nil .(n :: (S n ↑ k)) idp = inj₁ (idp , ((≡-sym (+-unit {n1})) , idp))
dec-long-lemma-disjoint-rev n k n1 (S k1) x pnx nil r p =
  let h1 = cut-t1 p
      h2 = cut-t2 p
  in  abs-refl (≤-trans (≤-reflexive (cong S (≡-sym h2))) (≤-trans pnx (≤-trans (≤-reflexive h1) (≤-up rrr))))
dec-long-lemma-disjoint-rev n k n1 0 x pnx (.n1 :: l) .(l ++ x :: n :: (S n ↑ k)) idp = inj₂ (l , (idp , idp))
dec-long-lemma-disjoint-rev n k n1 (S k1) x pnx (x₁ :: l) r p with (dec-long-lemma-disjoint-rev n k (S n1) k1 x pnx l r (cut-head p))
... | inj₁ (pl , px , pr) rewrite (cut-tail p) = inj₁ (((head+tail idp pl) , ((≡-trans px (≡-sym (+-three-assoc {n1} {1}))) , pr)))
... | inj₂ (m , pl , pr) rewrite (cut-tail p) = inj₂ (m , (head+tail idp pl , pr))

long-long-not-disjoint : (n k n1 k1 : ℕ) -> (k + n == S (k1 + n1))
                         -> Σ _ (λ mf -> ((k + n :: (n ↓ (2 + k)) ++ (n1 ↓ (2 + k1)) ++ (2 + (k1 + n1)) :: nil) ≅* mf) ×
                                        (((n ↓ (2 + k)) ++ (S (k1 + n1) :: (n1 ↓ (3 + k1)))) ≅* mf))
long-long-not-disjoint n 0 n1 k1 p rewrite p rewrite (cong {ℕ} {ℕ} S (+-comm n1 k1)) =
  let left = trans (cancel (_ :: _ :: nil) _) (trans (long-swap-lr n1 (2 + (k1 + n1)) (1 + k1) [ S (k1 + n1) ] [ 2 + k1 + n1 ] rrr) (trans (cancel _ nil) (idp≅* ++-unit)))
      right = trans (cancel [ _ ] _) (cancel nil _)
  in  _ , (left , right)
long-long-not-disjoint n (S k) n1 k1 p with k ≤? k1
long-long-not-disjoint n (S k) n1 k1 p | yes q =
  let left =
        ≅*begin
          1 + k + n :: (n ↓ (3 + k)) ++ (n1 ↓ (2 + k1)) ++ (2 + (k1 + n1)) :: nil
        ≅*⟨ idp≅* (≡-sym (++-assoc (1 + k + n :: (n ↓ (3 + k))) (n1 ↓ (2 + k1)) ((2 + (k1 + n1)) :: nil))) ⟩
          (1 + k + n :: 2 + k + n :: (n ↓ (2 + k)) ++ (n1 ↓ (2 + k1))) ++ (2 + (k1 + n1)) :: nil
        ≅*⟨ ++r [ _ ] (l++ (_ :: _ :: nil) (long-≤-long n k n1 k1 (≡-down2 p) q)) ⟩
          (1 + k + n :: 2 + k + n :: (n1 ↓ (1 + k1)) ++ ((1 + n) ↓ (1 + k))) ++ (2 + (k1 + n1)) :: nil
        ≅*⟨ ++r [ _ ] (l++ [ _ ] (long-swap-lr (n1) (2 + k + n) (1 + k1) nil (((1 + n) ↓ (1 + k))) (≤-reflexive (≡-sym (cong S p))))) ⟩
          (1 + k + n :: (n1 ↓ (1 + k1)) ++ 2 + k + n :: ((1 + n) ↓ (1 + k))) ++ (2 + (k1 + n1)) :: nil
        ≅*⟨ idp≅* (head+tail p (start+end (start+end (idp {a = (n1 ↓ (1 + k1))}) (head+tail (≡-sym (+-three-assoc {_} {1} {n})) idp)) idp)) ⟩
          (1 + (k1 + n1) :: (n1 ↓ (1 + k1)) ++ (1 + k + (1 + n)) :: ((1 + n) ↓ (1 + k))) ++ (2 + (k1 + n1)) :: nil
        ≅*⟨ idp ⟩
          ((n1 ↓ (2 + k1)) ++ ((1 + n) ↓ (2 + k))) ++ (2 + (k1 + n1)) :: nil
        ≅*⟨ short-swap-lr ((n1 ↓ (2 + k1))) nil (≤-trans (s≤s (≤-up-+ rrr)) (≤-reflexive p)) (≤-reflexive (≡-sym (cong S (≡-trans (+-three-assoc {k} {1} {n}) p)))) ⟩
          ((n1 ↓ (2 + k1)) ++ S (k1 + n1) :: (S n ↓ (2 + k))) ++ nil
        ≅*⟨ idp≅* ++-unit ⟩
          (n1 ↓ (2 + k1)) ++ S (k1 + n1) :: (S n ↓ (2 + k))
        ≅*⟨ short-swap-lr nil ((S n ↓ (2 + k))) (≤-up-+ rrr) rrr ⟩
          (k1 + n1) :: (n1 ↓ (2 + k1)) ++ ((1 + n) ↓ (2 + k))
        ≅*∎
      right =
        ≅*begin
          (n ↓ (3 + k)) ++ S (k1 + n1) :: (n1 ↓ (3 + k1))
        ≅*⟨ short-swap-lr {n} {1 + k} nil ((n1 ↓ (3 + k1))) (≤-trans (≤-up-+ rrr) (≤-reflexive (≡-down2 p))) ((≤-trans (≤-up rrr) (≤-reflexive (cong S (≡-sym p))))) ⟩
          (k1 + n1) :: (n ↓ (3 + k)) ++ (n1 ↓ (3 + k1))
        ≅*⟨ l++ [ _ ] (long-≤-long n (S k) n1 (S k1) p (s≤s q)) ⟩
          (k1 + n1) :: (n1 ↓ (2 + k1)) ++ ((1 + n) ↓ (2 + k))
        ≅*∎
  in  _ , left , right
long-long-not-disjoint n (S k) 0 k1 p | no q rewrite (+-unit {k1}) rewrite ≡-sym (≡-down2 p) = ⊥-elim (q (≤-up-r-+ rrr))
long-long-not-disjoint n (S k) (S n1) k1 p | no q =
  let left =
        ≅*begin
          1 + k + n :: 2 + k + n :: (n ↓ (2 + k)) ++ (((1 + n1) ↓ (2 + k1)) ++ (2 + (k1 + (1 + n1))) :: nil)
        ≅*⟨ idp≅* (≡-sym (++-assoc (1 + k + n :: 2 + k + n :: (n ↓ (2 + k))) ((1 + n1) ↓ (2 + k1)) ((2 + (k1 + (1 + n1))) :: nil))) ⟩
          (1 + k + n :: 2 + k + n :: (n ↓ (2 + k)) ++ ((1 + n1) ↓ (2 + k1))) ++ (2 + (k1 + (1 + n1))) :: nil
        ≅*⟨ ++r [ _ ] (l++ (_ :: _ :: nil) (long->-long n k n1 k1 (≡-trans (≡-down2 p) (+-three-assoc {k1} {1} {n1})) (≰⇒> q))) ⟩
          (1 + k + n :: 2 + k + n :: (n1 ↓ (2 + k1)) ++ (n ↓ (2 + k))) ++ (2 + (k1 + (1 + n1))) :: nil
        ≅*⟨ ++r [ _ ] (l++ [ _ ] (long-swap-lr n1 (2 + (k + n)) (2 + k1) nil (n ↓ (2 + k)) (≤-reflexive (≡-sym (≡-trans (cong S p) (+-three-assoc {2 + k1} {1})))))) ⟩
          (1 + k + n :: (n1 ↓ (2 + k1)) ++ 2 + k + n :: (n ↓ (2 + k))) ++ (2 + (k1 + (1 + n1))) :: nil
        ≅*⟨ idp≅* (head+tail (≡-trans p (+-three-assoc {1 + k1} {1})) idp) ⟩
          ((2 + (k1 + n1)) :: (n1 ↓ (2 + k1)) ++ (2 + k + n) :: (n ↓ (2 + k))) ++ (2 + (k1 + (1 + n1))) :: nil
        ≅*⟨ idp ⟩
          ((n1 ↓ (3 + k1)) ++ (n ↓ (3 + k))) ++ (2 + (k1 + (1 + n1))) :: nil
        ≅*⟨ short-swap-lr (n1 ↓ (3 + k1)) nil (≤-trans (≤-up (≤-up-+ rrr)) (≤-reflexive p)) (≤-reflexive (≡-sym (cong S p))) ⟩
          ((n1 ↓ (3 + k1)) ++ S (k1 + S n1) :: (n ↓ (3 + k))) ++ nil
        ≅*⟨ idp≅* ++-unit ⟩
          (n1 ↓ (3 + k1)) ++ S (k1 + S n1) :: (n ↓ (3 + k))
        ≅*⟨ short-swap-lr {n1} {1 + k1} nil (n ↓ (3 + k)) (≤-up-+ (≤-up rrr)) (≤-reflexive (+-three-assoc {1 + k1} {1})) ⟩
          (k1 + S n1) :: (n1 ↓ (3 + k1)) ++ (n ↓ (3 + k))
        ≅*∎
      right =
        ≅*begin
          (n ↓ (3 + k)) ++ S (k1 + (1 + n1)) :: ((1 + n1) ↓ (3 + k1))
        ≅*⟨ short-swap-lr {n} {1 + k} nil (((1 + n1) ↓ (3 + k1))) (≤-trans (≤-up-+ rrr) (≤-reflexive (≡-down2 p))) ((≤-trans (≤-up rrr) (≤-reflexive (cong S (≡-sym p))))) ⟩
          (k1 + (1 + n1)) :: (n ↓ (3 + k)) ++ ((1 + n1) ↓ (3 + k1))
        ≅*⟨ l++ [ _ ] (long->-long n (S k) n1 (S k1) (≡-trans p (+-three-assoc {1 + k1} {1} {n1})) (s≤s ((≰⇒> q)))) ⟩
          (k1 + (1 + n1)) :: (n1 ↓ (3 + k1)) ++ (n ↓ (3 + k))
        ≅*∎
  in  _ , left , right


long-long-lemma-rev : (n k n1 k1 : ℕ) -> (r l1 r1 : List) -> ((r ++ (1 + k + n) :: (n ↑ (2 + k))) == (r1 ++ (1 + k1 + n1) :: (n1 ↑ (2 + k1)) ++ l1))
                      -> Σ _ (λ mf -> (((((k + n) :: (n ↓ (2 + k)) ++ (rev r)) ≅* mf)) × (((rev l1) ++ (k1 + n1) :: (n1 ↓ (2 + k1)) ++ (rev r1)) ≅* mf)))
long-long-lemma-rev n k n1 k1 nil nil nil p
  rewrite (cut-t2 p)
  rewrite (ar-lemma k k1 (cut-t2 p) (cut-t1 p)) = _ , idp , idp
long-long-lemma-rev n k n1 k1 nil (x :: l) nil p =
  let nn1 = (cut-t2 p)
      kk1 = ar-lemma k k1 nn1 (cut-t1 p)
  in ⊥-elim (nil-abs (++-empty (S (k1 + n1) :: n1 :: S n1 :: (S (S n1) ↑ k1)) ((x :: l)) (≡-trans (≡-sym p)
    (head+tail (cut-tail p)
    (head+tail nn1
    (head+tail (cut-t3 p)
    (≡-trans (cong (λ e -> (2 + e) ↑ k) nn1) (cong (λ e -> (2 + n1) ↑ e) kk1))))))))
long-long-lemma-rev n 0 n1 k1 nil l1 (x :: x₁ :: x₂ :: nil) ()
long-long-lemma-rev n 0 n1 k1 nil l1 (x :: x₁ :: x₂ :: x₃ :: r1) ()
long-long-lemma-rev n (S k) n1 k1 nil l1 (x :: r1) p =
  let q = cut-head p
  in  ⊥-elim (dec-long-lemma-rev n (S (S (S k))) n1 (S (k1 + n1)) (≤-up (≤-up-+ rrr)) r1 (S n1 :: (S (S n1) ↑ k1) ++ l1) q)
long-long-lemma-rev n k n1 0 (x :: nil) l1 nil p =
  let a1 = cut-t2 p
      a2 = cut-t3 p
  in  abs-refl (≤-trans (≤-reflexive (≡-sym a2)) (≤-trans (≤-up (≤-up-+ rrr)) (≤-reflexive a1)))
long-long-lemma-rev n 0 .n 0 (.(S n) :: .n :: nil) .(n :: S n :: nil) nil idp = _ , ((trans (cancel (n :: S n :: nil) [ S n ]) (cancel _ nil)) , (trans (cancel [ S n ] _) (cancel nil _)))
long-long-lemma-rev n (S k) .(S (k + n)) 0 (.(S (S (k + n))) :: .(S (k + n)) :: nil) .(n :: S n :: S (S n) :: (S (S (S n)) ↑ k)) nil idp =
  let left =
        ≅*begin
          S (k + n) :: (n ↓ (3 + k)) ++ S (k + n) :: (2 + (k + n)) :: nil
        ≅*⟨ short-swap-lr {n = n} {k = 1 + k} [ S (k + n) ] [ 2 + (k + n) ] (≤-up-+ rrr) (≤-up rrr) ⟩
          S (k + n) :: k + n :: (n ↓ (3 + k)) ++ S (S (k + n)) :: nil
        ≅*⟨ short-swap-l {n = n} {k = 1 + k} (S (k + n) :: k + n :: nil) (≤-up (≤-up-+ rrr)) rrr ⟩
          S (k + n) :: k + n :: S (k + n) :: (n ↓ (3 + k))
        ≅*⟨ braid nil _ ⟩
          k + n :: S (k + n) :: k + n :: (n ↓ (3 + k))
        ≅*∎
      right =
        ≅*begin
          (((rev (S (S (S n)) ↑ k) ++ S (S n) :: nil) ++ S n :: nil) ++ n :: nil) ++ S (k + n) :: S (S (k + n)) :: S (k + n) :: nil
        ≅*⟨ ++r (S (k + n) :: S (S (k + n)) :: S (k + n) :: nil) (idp≅* (telescope-rev (S n) k (n :: nil))) ⟩
          _
        ≅*⟨ ++r (S (k + n) :: S (S (k + n)) :: S (k + n) :: nil) (idp≅* (++-↓ n (S (S k)))) ⟩
          (n ↓ (3 + k)) ++ S (k + n) :: S (S (k + n)) :: S (k + n) :: nil
        ≅*⟨ short-swap-lr {n} {1 + k} nil (_ :: _ :: nil) (≤-up-+ rrr) (≤-up rrr)  ⟩
          k + n :: (n ↓ (3 + k)) ++ S (S (k + n)) :: S (k + n) :: nil
        ≅*⟨ short-swap-lr {n} {1 + k} [ _ ] [ _ ] ((≤-up-+ rrr)) rrr ⟩
          _
        ≅*⟨ short-swap-l (_ :: _ :: nil) (≤-up-+ rrr) (≤-up rrr) ⟩
          k + n :: S (k + n) :: k + n :: (n ↓ (3 + k))
        ≅*∎
  in  _ , (left , right)
long-long-lemma-rev n k n1 0 (.(S n1) :: .n1 :: .(S n1) :: r) .(r ++ S (k + n) :: n :: S n :: (S (S n) ↑ k)) nil idp =
  let left =
        ≅*begin
          k + n :: (n ↓ (2 + k)) ++ ((rev r ++ S n1 :: nil) ++ n1 :: nil) ++ S n1 :: nil
        ≅*⟨ l++ (k + n :: (n ↓ (2 + k))) (idp≅* (≡-trans (++-assoc _ [ n1 ] [ S n1 ]) (++-assoc _ [ S n1 ] (n1 :: [ S n1 ])))) ⟩
          k + n :: (n ↓ (2 + k)) ++ rev r ++ S n1 :: n1 :: S n1 :: nil
        ≅*⟨ l++ (k + n :: (n ↓ (2 + k))) (braid (rev r) nil) ⟩
          k + n :: (n ↓ (2 + k)) ++ rev r ++ n1 :: S n1 :: n1 :: nil
        ≅*∎
      right =
        ≅*begin
          rev (r ++ S (k + n) :: (n ↑ (2 + k)))
        ≅*⟨ idp≅* (rev-++ r _) ⟩
          rev (S (k + n) :: (n ↑ (2 + k))) ++ (rev r)
        ≅*⟨ ++r (rev r) (idp≅* (start+end (rev-u n (S (S k))) (idp {a = [ S (k + n) ]}))) ⟩
          ((n ↓ (2 + k)) ++ [ S (k + n) ]) ++ (rev r)
        ≅*⟨ ++r (rev r) (short-swap-l nil (≤-up-+ rrr) rrr) ⟩
          k + n :: (n ↓ (2 + k)) ++ rev r
        ≅*∎
  in  _ , (left , trans (++r (n1 :: S n1 :: n1 :: nil) right) (idp≅* (++-assoc (k + n :: (n ↓ (2 + k))) (rev r) _)))
long-long-lemma-rev n k n1 (S k1) (x :: r) l1 nil p with (dec-long-lemma-disjoint-rev n (1 + k) n1 (2 + k1) (S (k + n)) (s≤s (≤-up-+ rrr)) r l1 (cut-head p))
long-long-lemma-rev n k n1 (S k1) (x :: r) l nil p | inj₁ (l1p , xp , r1p) rewrite (cut-t1 p) rewrite l1p rewrite r1p =
  let xpp = ≡-down2 (≡-trans xp (+-three-assoc {n1} {1} {1 + k1}))
      left =
        ≅*begin
          _
        ≅*⟨ l++ (k + n :: (n ↓ (2 + k))) (idp≅* (telescope-rev n1 k1 [ 2 + (k1 + n1) ])) ⟩
          k + n :: (n ↓ (2 + k)) ++ (n1 ↓ (2 + k1)) ++ (2 + (k1 + n1)) :: nil
        ≅*∎
      right =
        ≅*begin
          ((rev (S (S n) ↑ k) ++ S n :: nil) ++ n :: nil) ++ (S (k1 + n1) :: (n1 ↓ (3 + k1)) ++ nil)
        ≅*⟨ idp≅* (telescope-rev n k ((S (k1 + n1) :: (n1 ↓ (3 + k1)) ++ nil))) ⟩
          (n ↓ (2 + k)) ++ (S (k1 + n1) :: (n1 ↓ (3 + k1)) ++ nil)
        ≅*⟨ l++ (n ↓ (2 + k)) (idp≅* (++-unit)) ⟩
          (n ↓ (2 + k)) ++ (S (k1 + n1) :: (n1 ↓ (3 + k1)))
        ≅*∎
      rec-m , rec-l , rec-r  = long-long-not-disjoint n k n1 k1 (≡-trans xpp (≡-trans (+-three-assoc {n1} {1} {k1}) (cong S (+-comm n1 k1))))
  in rec-m , (trans left rec-l , trans right rec-r)
long-long-lemma-rev n k n1 (S k1) (x :: r) l nil p | inj₂ (m , lmp , mrp) rewrite (cut-t1 p) rewrite lmp rewrite mrp rewrite (rev-++ ((S (S (S n1)) ↑ k1)) m) =  -- disjoint
  let left =
        ≅*begin
          (((((rev m) ++ (rev ((S (S (S n1)) ↑ k1)))) ++ S (S n1) :: nil) ++ S n1 :: nil) ++ n1 :: nil) ++ S (S (k1 + n1)) :: nil
        ≅*⟨ idp≅* (telescope-l-rev-+1 n1 k1 (rev m) [ 2 + k1 + n1 ]) ⟩
          rev m ++ (n1 ↓ (3 + k1)) ++ (2 + k1 + n1) :: nil
        ≅*⟨ long (1 + k1) (rev m) nil ⟩
          _
        ≅*⟨ l++ (rev m) (idp≅* ++-unit) ⟩
          rev m ++ (1 + k1 + n1) :: (n1 ↓ (3 + k1))
        ≅*∎
      right =
        ≅*begin
          rev (m ++ S (k + n) :: n :: S n :: (S (S n) ↑ k)) ++ S (k1 + n1) :: S (S (k1 + n1)) :: S (k1 + n1) :: k1 + n1 :: (n1 ↓ k1) ++ nil
        ≅*⟨ ++r _ (idp≅* (rev-++ m _)) ⟩
          ((((rev (S (S n) ↑ k) ++ S n :: nil) ++ n :: nil) ++ S (k + n) :: nil) ++ rev m) ++ S (k1 + n1) :: (n1 ↓ (3 + k1)) ++ nil
        ≅*⟨ idp≅* (++-assoc _ (rev m) (S (k1 + n1) :: (n1 ↓ (3 + k1)) ++ nil)) ⟩
          _
        ≅*⟨ idp≅* (start+end (telescope-rev n k [ S (k + n) ]) idp) ⟩
          _
        ≅*⟨ l++ (((n ↓ (2 + k)) ++ S (k + n) :: nil)) (l++ (rev m) (idp≅* ++-unit)) ⟩
          _
        ≅*⟨ ++r ((rev m) ++ S (k1 + n1) :: (n1 ↓ (3 + k1))) (short-swap-l {n} {k} nil (≤-up-+ {r = k} rrr) rrr)  ⟩
          _
        ≅*∎
  in   _ , (l++ (k + n :: (n ↓ (2 + k))) left , right)
long-long-lemma-rev n k n1 k1 (x₁ :: r) l1 (x :: r1) p rewrite cut-tail p =
  let rec-m , rec-l , rec-r = long-long-lemma-rev n k n1 k1 r l1 r1 (cut-head p)
  in  (rec-m ++ [ x ]) , (trans (idp≅* (≡-sym (++-assoc _ (rev r) [ x ]))) (++r [ x ] rec-l) ,
                       (trans (idp≅* (≡-sym
                           (≡-trans (++-assoc (rev l1)  _   (x :: nil))
                           (≡-trans (cong (λ e -> rev l1 ++ k1 + n1 :: S (k1 + n1) :: k1 + n1 :: nil ++ e)
                                     (++-assoc (n1 ↓ k1) (rev r1) (x :: nil))) idp)))) (++r [ x ] rec-r)))

long-long-lemma : (n k n1 k1 : ℕ) -> (r l1 r1 : List) -> (((n ↓ (2 + k)) ++ (1 + k + n) :: r) == (l1 ++ (n1 ↓ (2 + k1)) ++ (1 + k1 + n1) :: r1)) -> Σ _ (λ mf -> (((((k + n) :: (n ↓ (2 + k)) ++ r) ≅* mf)) × ((l1 ++ (k1 + n1) :: (n1 ↓ (2 + k1)) ++ r1) ≅* mf)))
long-long-lemma n k n1 k1 r l1 r1 p rewrite (rev-rev {l1}) rewrite (rev-rev {r1}) rewrite (rev-rev {r}) =
  let pp =
        begin
          rev r ++ S (k + n) :: (n ↑ (2 + k))
        =⟨ ≡-sym (start+end (idp {a = rev r}) (head+tail idp (++-↑ n (1 + k)))) ⟩
          _
        =⟨ ≡-sym (start+end (idp {a = rev r}) (head+tail idp (start+end (++-↑ n k) idp))) ⟩
          rev r ++ (S (k + n) :: ((n ↑ k) ++ [ k + n ]) ++ S (k + n) :: nil)
        =⟨ ≡-sym (start+end (idp {a = rev r}) (head+tail idp (≡-sym (++-assoc (n ↑ k) (k + n :: nil) (S (k + n) :: nil))))) ⟩
          rev r ++ (S (k + n) :: ((n ↑ k) ++ (k + n :: S (k + n) :: nil)))
        =⟨ ≡-sym (++-assoc (rev r) (S (k + n) :: nil) ((n ↑ k) ++ k + n :: S (k + n) :: nil)) ⟩
          ((rev r ++ S (k + n) :: nil)) ++ ((n ↑ k) ++ k + n :: S (k + n) :: nil)
        =⟨ ≡-sym (++-assoc (rev r ++ S (k + n) :: nil) (n ↑ k) _) ⟩
          _
        =⟨ ≡-sym (++-assoc ((rev r ++ S (k + n) :: nil) ++ (n ↑ k)) (k + n :: nil) _) ⟩
          ((((rev r) ++ [ S (k + n) ]) ++ (n ↑ k)) ++ k + n :: nil) ++ S (k + n) :: nil
        =⟨ ≡-sym (start+end (start+end (start+end (start+end (≡-sym (rev-rev {rev r})) idp) (rev-d n k)) idp) idp) ⟩
          ((rev (S (k + n) :: rev (rev r)) ++ rev (n ↓ k)) ++ k + n :: nil) ++ S (k + n) :: nil
        =⟨ ≡-sym (start+end (start+end (rev-++ (n ↓ k) (S (k + n) :: rev (rev r))) idp) idp) ⟩
          (rev ((n ↓ k) ++ S (k + n) :: rev (rev r)) ++ k + n :: nil) ++ S (k + n) :: nil
        =⟨ cong rev p ⟩
          rev (rev (rev l1) ++ ((n1 ↓ (2 + k1)) ++ S (k1 + n1) :: rev (rev r1)))
        =⟨ rev-++ (rev (rev l1)) _ ⟩
          rev ((n1 ↓ (2 + k1)) ++ S (k1 + n1) :: rev (rev r1)) ++ rev (rev (rev l1))
        =⟨ start+end (rev-++ ((n1 ↓ (2 + k1))) _) idp ⟩
          ((rev (S (k1 + n1) :: rev (rev r1))) ++ rev (n1 ↓ (2 + k1))) ++ rev (rev (rev l1))
        =⟨ start+end (start+end (rev-++ [ S (k1 + n1) ] (rev (rev r1))) (rev-d n1 (2 + k1))) (≡-sym (rev-rev {rev l1})) ⟩
          (((rev (rev (rev r1))) ++ [ S (k1 + n1) ]) ++ (n1 ↑ (2 + k1))) ++ (rev l1)
        =⟨ start+end (start+end (start+end (≡-sym (rev-rev {rev r1})) idp) idp) idp ⟩
          (((rev r1) ++ [ S (k1 + n1) ]) ++ (n1 ↑ (2 + k1))) ++ (rev l1)
        =⟨ ++-assoc _ (n1 :: S n1 :: (S (S n1) ↑ k1)) (rev l1) ⟩
          _
        =⟨ ++-assoc (rev r1) _ (n1 :: S n1 :: (S (S n1) ↑ k1) ++ rev l1) ⟩
          rev r1 ++ S (k1 + n1) :: n1 :: S n1 :: (S (S n1) ↑ k1) ++ rev l1
        =∎
  in  long-long-lemma-rev n k n1 k1 (rev r) (rev l1) (rev r1) pp
