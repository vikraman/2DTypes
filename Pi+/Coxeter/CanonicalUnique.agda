{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module Pi+.Coxeter.CanonicalUnique where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.Coxeter.Arithmetic
open import Pi+.Coxeter.Lists
open import Pi+.Coxeter.MCoxeter
open import Pi+.Coxeter.CritPairsSwap
open import Pi+.Coxeter.MCoxeter
open import Pi+.Coxeter.Coxeter

open ≅*-Reasoning

data Canonical : (n : ℕ) -> Type₀ where
  CanZ : Canonical 0
  CanS : {n : ℕ} -> (l : Canonical n) -> {r : ℕ} -> (r ≤ S n) -> Canonical (S n)

immersion : {n : ℕ} -> Canonical n -> List
immersion {0} CanZ = nil
immersion {S n} (CanS l {r} r≤1+n) = (immersion l) ++ ((S n) ↓ r)

canonical-eta : {n : ℕ} -> {cl1 cl2 : Canonical n} -> {r1 r2 : ℕ} -> (rn1 : r1 ≤ (S n)) -> (rn2 : r2 ≤ (S n)) -> (cl1 == cl2) -> (pr : r1 == r2) 
    -> (CanS cl1 rn1) == (CanS cl2 rn2)
canonical-eta {n} {cl1} {cl2} rn1 rn2 pcl pr = 
    let lemma = ap (λ t -> CanS cl1 t) (≤-isProp (transport (λ r -> r ≤ (S n)) pr rn1) rn2)
        lemma2 = {! (transport (λ r → r ≤ S n) pr rn1)  !}
    in  lemma2 ∙ lemma ∙ ap (λ t -> CanS t rn2) pcl 

data _>>_ : ℕ -> List -> Set where
  nil : {n : ℕ} -> n >> nil
  _:⟨_⟩:_ : {n : ℕ} -> {l : List} -> (k : ℕ) -> (k < n) -> n >> l -> n >> (k :: l)

extract-proof : {n : ℕ} -> {l : List} -> {a : ℕ} -> (n >> (a :: l)) -> (a < n)
extract-proof (_ :⟨ p ⟩: _) = p

>>-++ : {n : ℕ} -> {l1 l2 : List} -> n >> l1 -> n >> l2 -> n >> (l1 ++ l2)
>>-++ {n} {nil} {l2} ll1 ll2 = ll2
>>-++ {n} {x :: l1} {l2} (.x :⟨ p ⟩: ll1) ll2 = x :⟨ p ⟩: (>>-++ ll1 ll2)

>>-↓ : (n k r : ℕ) -> (r + k ≤ n) -> (n >> (k ↓ r))
>>-↓ n k 0 p = nil
>>-↓ n k (S r) p = (r + k) :⟨ p ⟩: (>>-↓ n k r (≤-down p))

>>-S : {n : ℕ} -> {l : List} -> (n >> l) -> ((S n) >> l)
>>-S  nil = nil
>>-S  (k :⟨ p ⟩: l') = k :⟨ ≤-up p ⟩: >>-S l'

-- immersion->> : {n : ℕ} -> (cl : Canonical n) -> n >> immersion cl
-- immersion->> {.0} CanZ = nil
-- immersion->> {S n} (CanS {n} cl {r} rn) =
--   let p = immersion->> {n} cl
--   in  >>-++ (>>-S p) {!!} -- >>-++ (>>-S p) (>>-↓ _ _ _ {!!})

reverse->> : {n : ℕ} -> {l : List} -> (n >> l) -> n >> reverse l
reverse->> {n} {nil} ll = ll
reverse->> {n} {x :: l} (.x :⟨ x₁ ⟩: ll) = 
    let rec = reverse->> {n} {l} ll
    in  >>-++ rec ((x :⟨ x₁ ⟩: nil))

abs-≡ : {n : ℕ} -> S n == n -> ⊥
abs-≡ ()

abs-const-↓ : (n k a : ℕ) -> (l r : List) -> (n ↓ k) == (l ++ a :: a :: r) -> ⊥
abs-const-↓ n (S (S k)) a nil r p with ≡-trans (cut-t1 p) (≡-sym (cut-t2 p))
abs-const-↓ n (S (S k)) a nil r p | x = abs-≡ x
abs-const-↓ n (S k) a (x :: l) r p = abs-const-↓ n k a l r (cut-head p)

abs-2≡ : {n : ℕ} -> S (S n) == n -> ⊥
abs-2≡ ()

abs-inc-↓ : (n k a : ℕ) -> (l r : List) -> (n ↓ k) == (l ++ a :: S a :: r) -> ⊥
abs-inc-↓ n (S (S k)) a nil r p with ≡-trans (cong S (cut-t1 p)) (≡-sym (cut-t2 p))
abs-inc-↓ n (S (S k)) a nil r p | x = abs-2≡ x
abs-inc-↓ n (S k) a (x :: l) r p = abs-inc-↓ _ _ _ _ _ (cut-head p)

abs-jump-↓ : (n k a b : ℕ) -> (S a < b) -> (l r : List) -> (n ↓ k) == (l ++ b :: a :: r) -> ⊥
abs-jump-↓ n (S (S k)) a b x nil r p =
  let p1 = cut-t1 p
      p2 = cut-t2 p
      t1 : S (S (k + n)) ≤ S (k + n)
      t1 = ≤-trans (≤-reflexive (ap (λ t -> S (S t)) p2)) (≤-trans x (≤-reflexive (! p1)))
  in  abs-refl t1
abs-jump-↓ n (S k) a b x (e :: l) r p = abs-jump-↓ n k a b x l r (cut-head p)

-- --- And versions for 2-⇣

abs-const2-↓ : (n1 k1 n2 k2 a : ℕ) -> (n1 < n2) -> (l r : List) -> (n1 ↓ k1) ++ (n2 ↓ k2) == (l ++ a :: a :: r) -> ⊥
-- abs-const2-↓ 0 k1 n2 k2 a pnn l r p = abs-const-↓ _ _ _ l r p
-- abs-const2-↓ (S n1) 0 n2 k2 a pnn l r p = abs-const-↓ _ _ _ l r p
-- abs-const2-↓ (S 0) (S k1) (S .0) (S k2) .0 (s≤s ()) nil .nil refl
-- abs-const2-↓ (S (S n1)) (S 0) (S .(S n1)) (S k2) .(S n1) pnn nil .(S n1 ↓ k2) refl = (⊥-elim (1+n≰n pnn))
-- abs-const2-↓ (S n1) (S k1) n2 k2 a pnn (x :: l) r p = abs-const2-↓ n1 k1 n2 k2 a (≤-down pnn) l r (cut-head p)

abs-braid2-↓ : (n1 k1 n2 k2 a : ℕ) -> (n1 < n2) -> (l r : List) -> (n1 ↓ k1) ++ (n2 ↓ k2) == (l ++ S a :: a :: S a :: r) -> ⊥
abs-braid2-↓ n1 k1 n2 k2 a pnn l r p = {!!}

abs-jump2-↓ : (n1 k1 n2 k2 a b : ℕ) -> (n1 < n2) -> (S a < b) -> (l r : List) -> (n1 ↓ k1) ++ (n2 ↓ k2) == (l ++ b :: a :: r) -> ⊥
abs-jump2-↓ n1 k1 n2 k2 a b pnn pab l r p = {!!}

data _||_||_ (A : Set) (B : Set) (C : Set) : Set where
  R1 : A -> A || B || C
  R2 : B -> A || B || C
  R3 : C -> A || B || C

-- some technical lemmas about lists
lemma-l++2++r : (a : ℕ) -> (l1 r1 l2 r2 : List) -> (l1 ++ r1 == l2 ++ a :: a :: r2)
                -> (Σ (List × List) (λ (rl2 , rr2) -> (r2 == rl2 ++ rr2) × (l1 == l2 ++ a :: a :: rl2) × (r1 == rr2))) || -- the case when both a :: a are in left
                   (Σ (List × List) (λ (ll2 , lr2) -> (l2 == ll2 ++ lr2) × (l1 == ll2) × (r1 == lr2 ++ a :: a :: r2))) || -- the case when both a :: a are in right
                   ((l1 == l2 ++ [ a ]) × (r1 == a :: r2)) -- the case when one a is in left, and one in right
lemma-l++2++r a nil r1 l2 r2 p = R2 ((nil , l2) , (idp , (idp , p)))
lemma-l++2++r a (x :: nil) r1 nil r2 p =
  let h = cut-tail p
  in  R3 ((cong [_] h) , (cut-head p))
lemma-l++2++r a (x :: x₁ :: l1) r1 nil r2 p =
  let h1 = cut-tail p
      h2 = cut-tail (cut-head p)
  in  R1 ((l1 , r1) , (cut-head (cut-head (≡-sym p)) , (head+tail h1 (head+tail h2 idp)) , idp))
lemma-l++2++r a (x :: l1) r1 (x₁ :: l2) r2 p with lemma-l++2++r a l1 r1 l2 r2 (cut-head p)
... | R1 ((fst , snd) , fst₁ , fst₂ , snd₁) = R1 ((fst , snd) , (fst₁ , ((head+tail (cut-tail p) fst₂) , snd₁)))
... | R2 ((fst , snd) , fst₁ , fst₂ , snd₁) = R2 (((x₁ :: fst) , snd) , ((cong (λ e -> x₁ :: e) fst₁) , ((head+tail (cut-tail p) fst₂) , snd₁)))
... | R3 (fst , snd) = R3 (head+tail (cut-tail p) fst , snd)

--- and versions for many-↓
abs-const-many-↓ : (n a : ℕ) -> (l r : List) -> (cl : Canonical n) -> (immersion {n} cl) == (l ++ a :: a :: r) -> ⊥
abs-const-many-↓ .0 a nil r CanZ ()
abs-const-many-↓ .0 a (x :: l) r CanZ ()
abs-const-many-↓ (S n) a l r (CanS cl x) p with lemma-l++2++r _ (immersion cl) (S n ↓ _) _ _ p
... | R1 ((fst , snd) , fst₁ , fst₂ , snd₁) = abs-const-many-↓ _ _ _ fst cl fst₂
... | R2 ((fst , snd) , fst₁ , fst₂ , snd₁) = abs-const-↓ _ _ _ snd r snd₁
abs-const-many-↓ (S n) a l r (CanS cl {S r₁} x) p | R3 (fst , snd) = {!!}
  -- let h = cut-tail snd
  --     n>cl = immersion->> cl
  --     n>a = subst (λ e -> n >> e) (reverse-++-commute l [ a ]) (reverse->> (subst (λ e -> n >> e) fst n>cl))
  -- in  ⊥-elim (1+n≰n (≤-trans (≤-reflexive (cong S h)) {!!}))

abs-braid-many-↓ : (n a : ℕ) -> (l r : List) -> (cl : Canonical n) -> (immersion {n} cl) == (l ++ S a :: a :: S a :: r) -> ⊥
abs-braid-many-↓ .0 a nil r CanZ ()
abs-braid-many-↓ .0 a (x :: l) r CanZ ()
abs-braid-many-↓ .(S _) a l r (CanS cl x) p = {!!}

abs-jump-many-↓ : (n a b : ℕ) -> (S a < b) -> (l r : List) -> (cl : Canonical n) -> (immersion {n} cl) == (l ++ b :: a :: r) -> ⊥
abs-jump-many-↓ .0 a b pab nil r CanZ ()
abs-jump-many-↓ .0 a b pab (x :: l) r CanZ ()
abs-jump-many-↓ .(S _) a b pab l r (CanS cl x) p = {!!}

only-one≅-↓ : (n k1 k2 : ℕ)  -> (k1 ≤ n) -> (k2 ≤ n) -> ((n ↓ k1) ≅ (n ↓ k2)) -> ⊥
-- only-one≅-↓ n k1 k2 pk1 pk2 (cancel≅ l r .(n ↓ k1) .(n ↓ k2) defm defmf) = abs-const-↓ _ _ _ l r defm
-- only-one≅-↓ n k1 k2 pk1 pk2 (swap≅ x l r .(n ↓ k1) .(n ↓ k2) defm defmf) = abs-jump-↓ _ _ _ _ x l r defm
-- only-one≅-↓ n k1 k2 pk1 pk2 (braid≅ l r .(n ↓ k1) .(n ↓ k2) defm defmf) = abs-inc-↓ _ _ _ l (_ :: r) defmf

++-:: : {n : ℕ} -> {l r : List} -> l ++ n :: r == (l ++ [ n ]) ++ r
++-:: {n} {l} {r} = ≡-sym (++-assoc l (n :: nil) r)

abs≅-↓ : (n k : ℕ) -> (k ≤ n) -> (m : List) -> ((n ↓ k) ≅ m) -> ⊥
-- abs≅-↓ n k pk m (cancel≅ l r .(n ↓ k) .m defm defmf) = abs-const-↓ _ _ _ l r defm
-- abs≅-↓ n k pk m (swap≅ x l r .(n ↓ k) .m defm defmf) = abs-jump-↓ _ _ _ _ x l r defm
-- abs≅-↓ n k pk m (braid≅ {n₁} l r .(n ↓ k) .m defm defmf) =
--   let lemma = ≡-trans defm ++-::
--   in  abs-inc-↓ n k n₁ (l ++ [ S n₁ ]) r lemma

abs2≅-↓ : (n1 k1 n2 k2 : ℕ) -> (k1 ≤ n1) -> (k2 ≤ n2) -> (n1 < n2) -> (m : List) -> ((n1 ↓ k1) ++ (n2 ↓ k2)) ≅ m -> ⊥
-- abs2≅-↓ n1 k1 n2 k2 pkn1 pkn2 pnn m (cancel≅ l r .((n1 ↓ k1) ++ (n2 ↓ k2)) .m defm defmf) = abs-const2-↓ n1 k1 n2 k2 _ pnn l r defm
-- abs2≅-↓ n1 k1 n2 k2 pkn1 pkn2 pnn m (swap≅ x l r .((n1 ↓ k1) ++ (n2 ↓ k2)) .m defm defmf) = abs-jump2-↓ n1 k1 n2 k2 _ _ pnn x l r defm
-- abs2≅-↓ n1 k1 n2 k2 pkn1 pkn2 pnn m (braid≅ l r .((n1 ↓ k1) ++ (n2 ↓ k2)) .m defm defmf) = abs-braid2-↓ n1 k1 n2 k2 _ pnn l r defm

only-one-canonical≅ : {n : ℕ} -> (cl : Canonical n) -> (m : List) -> (immersion {n} cl) ≅ m -> ⊥
-- only-one-canonical≅ cl m (cancel≅ l r .(immersion cl) .m defm defmf) = abs-const-many-↓ _ _ _ r cl defm
-- only-one-canonical≅ cl m (swap≅ x l r .(immersion cl) .m defm defmf) = abs-jump-many-↓ _ _ _ x l r cl defm
-- only-one-canonical≅ cl m (braid≅ l r .(immersion cl) .m defm defmf) = abs-braid-many-↓ _ _ _ r cl defm

≡-↓ : (n k1 k2 : ℕ) -> (k1 ≤ n) -> (k2 ≤ n) -> ((n ↓ k1) == (n ↓ k2)) -> (k1 == k2)
≡-↓ 0 .0 .0 z≤n z≤n p = idp
≡-↓ (S n) 0 0 pk1 pk2 p = idp
≡-↓ (S n) (S k1) (S k2) pk1 pk2 p =
  let lemma = (cut-head p)
      rec = ≡-↓ _ _ _ (≤-down2 pk1) (≤-down2 pk2) {!!}
  in  cong S rec

≡-++↓ : (m1 m2 : List) -> (n k1 k2 : ℕ) -> (ml1 : n >> m1) -> (ml2 : n >> m2) -> (k1 ≤ S n) -> (k2 ≤ S n) -> (m1 ++ ((S n) ↓ k1) == m2 ++ ((S n) ↓ k2)) -> (k1 == k2) × (m1 == m2)
-- ≡-++↓ nil nil n k1 k2 ml1 ml2 pk1 pk2 p = (≡-↓ _ _ _ pk1 pk2 p) , idp
-- ≡-++↓ nil (x :: m2) (S n) (S k1) k2 ml1 (.x :⟨ x₁ ⟩: ml2) pk1 pk2 p =
--   let r = cut-tail  p
--   in  ⊥-elim (1+n≰n (≤-trans ? (≤-down2 x₁)))
-- ≡-++↓ (x :: m1) nil (S n) k1 (S k2) (.x :⟨ x₁ ⟩: ml1) ml2 pk1 pk2 p =
--   let r = cut-tail  p
--   in  ⊥-elim (1+n≰n (≤-trans (≤-reflexive (≡-sym r)) (≤-down2 x₁)))
-- ≡-++↓ (x :: m1) (x₁ :: m2) n k1 k2 (.x :⟨ x₂ ⟩: ml1) (.x₁ :⟨ x₃ ⟩: ml2) pk1 pk2 p =
--   let t = cut-head  p
--       h = cut-tail  p
--       hh , tt = ≡-++↓ m1 m2 n k1 k2 ml1 ml2 pk1 pk2 t
--   in  hh , subst (λ z → x :: m1 == z :: m2) h (cong (λ e -> x :: e) tt)


≡immersion : {n : ℕ} -> (cl1 cl2 : Canonical n) -> (immersion {n} cl1 == immersion {n} cl2) -> cl1 == cl2
≡immersion CanZ CanZ idp = idp
≡immersion {n} (CanS cl1 {r = r} x) (CanS cl2 {r = r₁} x₁) p = {!!}
  -- let n>>cl1 = immersion->> cl1
  --     n>>cl2 = immersion->> cl2
  --     lemma-r , lemma-cl = ≡-++↓ _ _ _ _ _ n>>cl1 n>>cl2 x x₁ p
  --     rec = ≡immersion cl1 cl2 lemma-cl
  -- in  canonical-eta x x₁ rec lemma-r

only-one-canonical≅* : {n : ℕ} -> (cl1 cl2 : Canonical n) -> (m1 m2 : List) -> (immersion {n} cl1 == m1) -> (immersion {n} cl2 == m2) -> (m1 ≅* m2)-> cl1 == cl2
only-one-canonical≅* cl1 cl2 m1 .m1 pm1 pm2 idp = ≡immersion _ _ (≡-trans pm1 (≡-sym pm2))
only-one-canonical≅* cl1 cl2 m1 m2 pm1 pm2 (trans≅ x p) =
  let ss = transport (λ t → t ≅ _) (! pm1) x
  in  ⊥-elim (only-one-canonical≅ cl1 _ ss)

only-one-canonical≃ : {n : ℕ} -> (cl1 cl2 : Canonical n) -> (m1 m2 : List) -> (immersion {n} cl1 == m1) -> (immersion {n} cl2 == m2) -> (m1 ≃ m2) -> cl1 == cl2
-- only-one-canonical≃ cl1 cl2 m1 .m1 pm1 pm2 (R idp idp) = ≡immersion _ _ (≡-trans pm1 (≡-sym pm2))
-- only-one-canonical≃ cl1 cl2 m1 m2 pm1 pm2 (R idp (trans≅ x p2)) =
--   let ss = subst (λ t → t ≅ _) (≡-sym pm2) x
--   in  ⊥-elim (only-one-canonical≅ cl2 _ ss)
-- only-one-canonical≃ cl1 cl2 m1 m2 pm1 pm2 (R (trans≅ x p1) p2) =
--   let ss = subst (λ t → t ≅ _) (≡-sym pm1) x
--   in  ⊥-elim (only-one-canonical≅ cl1 _ ss)
