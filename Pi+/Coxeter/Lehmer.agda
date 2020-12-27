{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module Pi+.Coxeter.Lehmer where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.Coxeter.Arithmetic
open import Pi+.Coxeter.Lists
open import Pi+.Coxeter.ReductionRel
open import Pi+.Coxeter.ImpossibleLists
open import Pi+.Coxeter.MCoxeter

open ≅*-Reasoning

data Lehmer : (n : ℕ) -> Type₀ where
  CanZ : Lehmer 0
  CanS : {n : ℕ} -> (l : Lehmer n) -> {r : ℕ} -> (r ≤ S n) -> Lehmer (S n)

immersion : {n : ℕ} -> Lehmer n -> List
immersion {0} CanZ = nil
immersion {S n} (CanS l {r} r≤1+n) = (immersion l) ++ (((S n) ∸ r) ↓ r)

-- l0 : Lehmer 0
-- l0 = CanZ
-- l1 : Lehmer 1
-- l1 = CanS {0} CanZ {1} (s≤s z≤n)
-- l2 : Lehmer 2
-- l2 = CanS l1 {2} (s≤s (s≤s z≤n))

-- ll2 : List
-- ll2 = immersion {2} l2

canonical-lift : {n : ℕ} -> (m : ℕ) -> (n ≤ m) -> (cln : Lehmer n) -> Σ (Lehmer m) (λ clm -> immersion {m} clm == immersion {n} cln)
canonical-lift {n} m p cln with ≤-∃ _ _ p
canonical-lift {.m} m p cln | 0 , idp = cln , idp
canonical-lift {n} .(S (fst + n)) p cln | S fst , idp =
  let rec-m , rec-p = canonical-lift {n} (fst + n) (≤-up-+ rrr) cln
  in  (CanS rec-m z≤n) , (≡-trans ++-unit rec-p)

canonical-append : {n : ℕ} -> (cl : Lehmer n) -> (x : ℕ) -> (n ≤ x) -> Σ _ (λ clx -> immersion {S x} clx == immersion {n} cl ++ [ x ])
canonical-append cl x px =
  let lifted-m , lifted-p = canonical-lift x px cl
  in  CanS lifted-m (s≤s z≤n) , start+end lifted-p idp

postulate
  lehmer-eta : {n : ℕ} -> {cl1 cl2 : Lehmer n} -> {r1 r2 : ℕ} -> (rn1 : r1 ≤ (S n)) -> (rn2 : r2 ≤ (S n)) -> (cl1 == cl2) -> (r1 == r2) -> (CanS cl1 rn1) == (CanS cl2 rn2)

data _>>_ : ℕ -> List -> Type₀ where
  nil : {n : ℕ} -> n >> nil
  _:⟨_⟩:_ : {n : ℕ} -> {l : List} -> (k : ℕ) -> (k < n) -> n >> l -> n >> (k :: l)

extract-proof : {n : ℕ} -> {l : List} -> {a : ℕ} -> (n >> (a :: l)) -> (a < n)
extract-proof (_ :⟨ p ⟩: _) = p

final≅-↓ : (n k1 : ℕ) -> (m : List) -> (n ↓ k1) ≅ m -> ⊥
final≅-↓ n k1 m (cancel≅ {n₁} l r .(n ↓ k1) .m defm defmf) = repeat-long-lemma n k1 n₁ l r defm
final≅-↓ n k1 m (swap≅ x l r .(n ↓ k1) .m defm defmf) = incr-long-lemma _ _ _ _ x l r defm
final≅-↓ n k1 m (long≅ {n₁} k l r .(n ↓ k1) .m defm defmf) =
  repeat-spaced-long-lemma n k1 (S (k + n₁)) l ((n₁ ↓ (1 + k))) r defm

-- a helper trichotomy type
data _||_||_ (A : Type₀) (B : Type₀) (C : Type₀) : Type₀ where
  R1 : A -> A || B || C
  R2 : B -> A || B || C
  R3 : C -> A || B || C

-- a technical lemma about splitting lists
lemma-l++2++r : (a b : ℕ) -> (l1 r1 l2 r2 : List) -> (l1 ++ r1 == l2 ++ a :: b :: r2)
                -> (Σ (List × List) (λ (rl2 , rr2) -> (r2 == rl2 ++ rr2) × (l1 == l2 ++ a :: b :: rl2) × (r1 == rr2))) || -- the case when both a :: b are in left
                   (Σ (List × List) (λ (ll2 , lr2) -> (l2 == ll2 ++ lr2) × (l1 == ll2) × (r1 == lr2 ++ a :: b :: r2))) || -- the case when both a :: b are in right
                   ((l1 == l2 ++ [ a ]) × (r1 == b :: r2)) -- the case when one a is in left, and b in right
lemma-l++2++r a b nil r1 l2 r2 p = R2 ((nil , l2) , (idp , (idp , p)))
lemma-l++2++r a b (x :: nil) r1 nil r2 p =
  let h = cut-tail p
  in  R3 ((cong [_] h) , (cut-head p))
lemma-l++2++r a b (x :: x₁ :: l1) r1 nil r2 p =
  let h1 = cut-tail p
      h2 = cut-tail (cut-head p)
  in  R1 ((l1 , r1) , (cut-head (cut-head (≡-sym p)) , (head+tail h1 (head+tail h2 idp)) , idp))
lemma-l++2++r a b (x :: l1) r1 (x₁ :: l2) r2 p with lemma-l++2++r a b l1 r1 l2 r2 (cut-head p)
... | R1 ((fst , snd) , fst₁ , fst₂ , snd₁) = R1 ((fst , snd) , (fst₁ , ((head+tail (cut-tail p) fst₂) , snd₁)))
... | R2 ((fst , snd) , fst₁ , fst₂ , snd₁) = R2 (((x₁ :: fst) , snd) , ((cong (λ e -> x₁ :: e) fst₁) , ((head+tail (cut-tail p) fst₂) , snd₁)))
... | R3 (fst , snd) = R3 (head+tail (cut-tail p) fst , snd)

final≅-↓-↓ : (n k n1 k1 : ℕ) -> (m : List) -> (k + n < k1 + n1) -> ((n ↓ k) ++ (n1 ↓ k1)) ≅ m -> ⊥
final≅-↓-↓ n k n1 k1 m pkn (cancel≅ {n₁} l r .((n ↓ k) ++ (n1 ↓ k1)) .m defm defmf) with (lemma-l++2++r n₁ n₁ (n ↓ k) (n1 ↓ k1) l r defm)
final≅-↓-↓ n k n1 k1 m pkn (cancel≅ {n₁} l r .(n ↓ k ++ n1 ↓ k1) .m defm defmf) | R1 (x , fst₁ , fst₂ , snd₁) = 
    dec-long-lemma n k n₁ n₁ (≤-reflexive idp) l (fst x) fst₂
final≅-↓-↓ n k n1 k1 m pkn (cancel≅ {n₁} l r .(n ↓ k ++ n1 ↓ k1) .m defm defmf) | R2 (x , fst₁ , fst₂ , snd₁) = 
    dec-long-lemma n1 k1 n₁ n₁ (≤-reflexive idp) (snd x) r snd₁
final≅-↓-↓ n k n1 k1 m pkn (cancel≅ {n₁} l r .(n ↓ k ++ n1 ↓ k1) .m defm defmf) | R3 x = {!   !}
final≅-↓-↓ n k n1 k1 m pkn (swap≅ x l r .((n ↓ k) ++ (n1 ↓ k1)) .m defm defmf) with (lemma-l++2++r _ _ (n ↓ k) (n1 ↓ k1) l r defm)
... | q = {!   !}
final≅-↓-↓ n k n1 k1 m pkn (long≅ k₁ l r .((n ↓ k) ++ (n1 ↓ k1)) .m defm defmf) = {!   !}

++-assoc-≡ : {l r1 r2 m : List} -> m == ((l ++ r1) ++ r2) -> m == (l ++ (r1 ++ r2))
++-assoc-≡ {l} {r1} {r2} {m} p = ≡-trans p (++-assoc l r1 r2)

final≅-Lehmer : {n : ℕ} -> (cl : Lehmer n) -> (m mf : List) -> (defm : m == (immersion {n} cl)) -> m ≅ mf -> ⊥
final≅-Lehmer {0} CanZ .nil mf idp p = empty-reduction p
final≅-Lehmer {S 0} (CanS CanZ {0} x) .nil mf idp p = empty-reduction p
final≅-Lehmer {S 0} (CanS CanZ {S 0} (s≤s x)) .(0 :: nil) mf idp p = one-reduction p
final≅-Lehmer {S (S n)} (CanS (CanS cl x₁) x) m mf defm (cancel≅ {n₁} l r .m .mf defm₁ defmf) rewrite (++-assoc-≡ {l = immersion cl} defm) with (lemma-l++2++r n₁ n₁ (immersion cl) _ l r defm₁)
final≅-Lehmer {S (S n)} (CanS (CanS cl x₁) x) m mf defm (cancel≅ {n₁} l r .m .mf defm₁ defmf) | R1 x₂ = {!   !}
final≅-Lehmer {S (S n)} (CanS (CanS cl x₁) x) m mf defm (cancel≅ {n₁} l r .m .mf defm₁ defmf) | R2 x₂ = {!   !}
final≅-Lehmer {S (S n)} (CanS (CanS cl x₁) x) m mf defm (cancel≅ {n₁} l r .m .mf defm₁ defmf) | R3 x₂ = {!   !}
final≅-Lehmer {S (S n)} (CanS (CanS cl x₁) x) m mf defm (swap≅ x₂ l r .m .mf defm₁ defmf) rewrite (++-assoc-≡ {l = immersion cl} defm) with (lemma-l++2++r _ _ (immersion cl) _ l r defm₁)
... | p = {!   !}
final≅-Lehmer {S (S n)} (CanS (CanS cl x₁) x) m mf defm (long≅ k l r .m .mf defm₁ defmf) = {!   !}


≡-↓ : (n k1 k2 : ℕ) -> (k1 ≤ n) -> (k2 ≤ n) -> ((n ↓ k1) == (n ↓ k2)) -> (k1 == k2)
≡-↓ 0 .0 .0 z≤n z≤n p = idp
≡-↓ (S n) 0 0 pk1 pk2 p = idp
≡-↓ (S n) (S k1) (S k2) pk1 pk2 p =
  let lemma = (cut-head p)
      rec = ≡-↓ _ _ _ (≤-down2 pk1) (≤-down2 pk2) {!!}
  in  cong S rec

≡-++↓ : (m1 m2 : List) -> (n k1 k2 : ℕ) -> (ml1 : n >> m1) -> (ml2 : n >> m2) -> (k1 ≤ S n) -> (k2 ≤ S n) -> (m1 ++ ((S n ∸ k1) ↓ k1) == m2 ++ ((S n ∸ k2) ↓ k2)) -> (k1 == k2) × (m1 == m2)
≡-++↓ nil nil n O O ml1 ml2 pk1 pk2 p = idp , idp
≡-++↓ nil nil O (S .0) (S .0) ml1 ml2 (s≤s z≤n) (s≤s z≤n) p = idp , idp
≡-++↓ nil nil (S n) (S k1) (S k2) ml1 ml2 pk1 pk2 p = 
  let rec-k , rec-l = ≡-++↓ nil nil n k1 k2 nil nil (≤-down2 pk1) (≤-down2 pk2) (cut-head p)
  in  (ap S rec-k) , idp
≡-++↓ nil (x :: m2) n (S k1) k2 ml1 (.x :⟨ x₁ ⟩: ml2) pk1 pk2 p = 
  let c = cut-tail p
  in  ⊥-elim (1+n≰n (≤-trans (≤-reflexive (ap S c)) (≤-trans x₁ (≤-reflexive (! (plus-minus (≤-down2 pk1)))))))
≡-++↓ (x :: m1) nil n k1 (S k2) (.x :⟨ x₁ ⟩: ml1) ml2 pk1 pk2 p = 
  let c = cut-tail p
  in  ⊥-elim (1+n≰n (≤-trans (≤-reflexive (ap S (! c))) ((≤-trans x₁ (≤-reflexive (! (plus-minus (≤-down2 pk2))))))))
≡-++↓ (x :: m1) (x₁ :: m2) n k1 k2 (.x :⟨ x₂ ⟩: ml1) (.x₁ :⟨ x₃ ⟩: ml2) pk1 pk2 p =
  let rec-k , rec-l = ≡-++↓ m1 m2 n k1 k2 ml1 ml2 pk1 pk2 (cut-head p)
      heads = cut-tail p
  in  rec-k , head+tail heads rec-l

-- ≡-++↓ : (m1 m2 : List) -> (n k1 k2 : ℕ) -> (ml1 : n >> m1) -> (ml2 : n >> m2) -> (k1 ≤ S n) -> (k2 ≤ S n) -> (m1 ++ ((S n) ↓ k1) == m2 ++ ((S n) ↓ k2)) -> (k1 == k2) × (m1 == m2)
-- ≡-++↓ nil nil n k1 k2 ml1 ml2 pk1 pk2 p = (≡-↓ _ _ _ pk1 pk2 p) , idp
-- ≡-++↓ nil (x :: m2) (S n) (S k1) k2 ml1 (.x :⟨ x₁ ⟩: ml2) pk1 pk2 p =
--   let r = cut-tail  p
--       lemma = (≤-trans (≤-up (≤-reflexive idp)) (introduce-≤-from-+ {S (S n)} {k1} {x} (+-comm (S (S n)) k1 ∙ r))) 
--   in  ⊥-elim (1+n≰n (≤-trans lemma (≤-down2 x₁)))
-- ≡-++↓ (x :: m1) nil (S n) k1 (S k2) (.x :⟨ x₁ ⟩: ml1) ml2 pk1 pk2 p =
--   let r = cut-tail  p
--       lemma = (≤-trans (≤-up (≤-reflexive idp)) (introduce-≤-from-+ {S (S n)} {k2} {x} (+-comm (S (S n)) k2 ∙ ! r))) 
--   in  ⊥-elim (1+n≰n {n} (≤-trans lemma (≤-down2 {n} {x} x₁)))
-- ≡-++↓ (x :: m1) (x₁ :: m2) n k1 k2 (.x :⟨ x₂ ⟩: ml1) (.x₁ :⟨ x₃ ⟩: ml2) pk1 pk2 p =
--   let t = cut-head  p
--       h = cut-tail  p
--       hh , tt = ≡-++↓ m1 m2 n k1 k2 ml1 ml2 pk1 pk2 t
--   in  hh , transport (λ z → x :: m1 == z :: m2) h (ap (λ e -> x :: e) tt)

>>-++ : {n : ℕ} -> {l1 l2 : List} -> n >> l1 -> n >> l2 -> n >> (l1 ++ l2)
>>-++ {n} {nil} {l2} ll1 ll2 = ll2
>>-++ {n} {x :: l1} {l2} (.x :⟨ p ⟩: ll1) ll2 = x :⟨ p ⟩: (>>-++ ll1 ll2)

>>-↓ : (n k r : ℕ) -> (r + k ≤ n) -> (n >> (k ↓ r))
>>-↓ n k 0 p = nil
>>-↓ n k (S r) p = (r + k) :⟨ p ⟩: (>>-↓ n k r (≤-down p))

>>-S : {n : ℕ} -> {l : List} -> (n >> l) -> ((S n) >> l)
>>-S  nil = nil
>>-S  (k :⟨ p ⟩: l') = k :⟨ ≤-up p ⟩: >>-S l'

immersion->> : {n : ℕ} -> (cl : Lehmer n) -> n >> immersion cl
immersion->> {.0} CanZ = nil
immersion->> {S n} (CanS {n} cl {r} rn) =
  let p = immersion->> {n} cl
  in  >>-++ (>>-S p) (>>-↓ (S n) (S n ∸ r) r (≤-reflexive (plus-minus rn)))

≡immersion : {n : ℕ} -> (cl1 cl2 : Lehmer n) -> (immersion {n} cl1 == immersion {n} cl2) -> cl1 == cl2
≡immersion CanZ CanZ idp = idp
≡immersion {n} (CanS cl1 {r = r} x) (CanS cl2 {r = r₁} x₁) p = 
  let n>>cl1 = immersion->> cl1
      n>>cl2 = immersion->> cl2
      lemma-r , lemma-cl = ≡-++↓ _ _ _ _ _ n>>cl1 n>>cl2 x x₁ p
      rec = ≡immersion cl1 cl2 lemma-cl
  in lehmer-eta x x₁ rec lemma-r

only-one-canonical≅* : {n : ℕ} -> (cl1 cl2 : Lehmer n) -> (m1 m2 : List) -> (immersion {n} cl1 == m1) -> (immersion {n} cl2 == m2) -> (m1 ≅* m2)-> cl1 == cl2
only-one-canonical≅* cl1 cl2 m1 .m1 pm1 pm2 idp = ≡immersion _ _ (≡-trans pm1 (≡-sym pm2))
only-one-canonical≅* cl1 cl2 m1 m2 pm1 pm2 (trans≅ x p) =
  let ss = transport (λ t → t ≅ _) (! pm1) x
  in  ⊥-elim (final≅-Lehmer cl1 (immersion cl1) _ idp ss)

only-one-canonical≃ : {n : ℕ} -> (cl1 cl2 : Lehmer n) -> (m1 m2 : List) -> (immersion {n} cl1 == m1) -> (immersion {n} cl2 == m2) -> (m1 ≃ m2) -> cl1 == cl2
only-one-canonical≃ cl1 cl2 m1 .m1 pm1 pm2 (comm≅ idp idp) = ≡immersion _ _ (≡-trans pm1 (≡-sym pm2))
only-one-canonical≃ cl1 cl2 m1 m2 pm1 pm2 (comm≅ idp (trans≅ x p2)) =
  let ss = transport (λ t → t ≅ _) (≡-sym pm2) x
  in  ⊥-elim (final≅-Lehmer cl2 _ _ idp ss)
only-one-canonical≃ cl1 cl2 m1 m2 pm1 pm2 (comm≅ (trans≅ x p1) p2) =
  let ss = transport (λ t → t ≅ _) (≡-sym pm1) x
  in  ⊥-elim (final≅-Lehmer cl1 _ _ idp ss)