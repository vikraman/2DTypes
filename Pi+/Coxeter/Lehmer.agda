{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module Pi+.Coxeter.Lehmer where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.Coxeter.Arithmetic
open import Pi+.Coxeter.Lists
open import Pi+.Coxeter.MCoxeter
open import Pi+.Coxeter.CritPairsImpossible

open ≅*-Reasoning

data Lehmer : (n : ℕ) -> Type₀ where
  CanZ : Lehmer 0
  CanS : {n : ℕ} -> (l : Lehmer n) -> {r : ℕ} -> (r ≤ S n) -> Lehmer (S n)

immersion : {n : ℕ} -> Lehmer n -> List
immersion {0} CanZ = nil
immersion {S n} (CanS l {r} r≤1+n) = (immersion l) ++ (((S n) ∸ r) ↓ r)

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
  canonical-eta : {n : ℕ} -> {cl1 cl2 : Lehmer n} -> {r1 r2 : ℕ} -> (rn1 : r1 ≤ (S n)) -> (rn2 : r2 ≤ (S n)) -> (cl1 == cl2) -> (r1 == r2) -> (CanS cl1 rn1) == (CanS cl2 rn2)

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

data _||_||_ (A : Set) (B : Set) (C : Set) : Type₀ where
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
... | q = {! q  !}
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
... | p = {!   !}
final≅-Lehmer {S (S n)} (CanS (CanS cl x₁) x) m mf defm (swap≅ x₂ l r .m .mf defm₁ defmf) rewrite (++-assoc-≡ {l = immersion cl} defm) with (lemma-l++2++r _ _ (immersion cl) _ l r defm₁)
... | p = {!   !}
final≅-Lehmer {S (S n)} (CanS (CanS cl x₁) x) m mf defm (long≅ k l r .m .mf defm₁ defmf) = {!   !}
