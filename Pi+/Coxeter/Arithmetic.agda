{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Arithmetic where

open import lib.Base
open import lib.types.Nat
open import lib.PathGroupoid

≤-up : {n m : ℕ} -> m ≤ n -> m ≤ S n
≤-up = lteSR

≤-down : {n m : ℕ} -> S m ≤ n -> m ≤ n
≤-down {n} {m} (inl x) = ≤-cancel-S (inr ((transport (λ t -> t < S n) (! x) ltS)))
≤-down {n} {m} (inr x) = ≤-cancel-S (inr (<-trans x ltS))

≤-down2 : {n m : ℕ} -> S m ≤ S n -> m ≤ n
≤-down2 = ≤-cancel-S

≤-abs : {A : Type₀} -> {n : ℕ} -> (S n ≤ 0) -> A
≤-abs {_} {n} p = ⊥-elim (S≰O n p)

abs-refl : {A : Type₀} -> {n : ℕ} -> n < n -> A
abs-refl {_} {S n} p = abs-refl (<-cancel-S p)

abs-suc : {A : Type₀} -> {n : ℕ} -> S n < n -> A
abs-suc {_} {S n} p = abs-suc (<-cancel-S p)

infixl 81 _∸_
_∸_ : ℕ → ℕ → ℕ
m ∸ 0   =  m
0 ∸ S n  =  0
S m ∸ S n  =  m ∸ n

≡-down2 : {p q : ℕ} -> (S p == S q) -> p == q   
≡-down2 {p} {q} r = ℕ-S-is-inj p q r

postulate
    ∸-implies-≤ : {p q r : ℕ} -> (p == (q ∸ r)) -> (p ≤ q)
    ≤-remove-+ : {p q r : ℕ} -> (p + q ≤ r) -> (q ≤ r)
    introduce-≤-from-+ : {p q r : ℕ} -> (p + q == r) -> (p ≤ r)
    +-three-assoc : {k i r : ℕ} -> k + (i + r) == (i + k) + r
    introduce-∸ : {p q r : ℕ} -> (r ≤ q) -> (p + r == q) -> (p == (q ∸ r))
    eliminate-∸ : {p q r : ℕ} -> (r ≤ q) -> (p == q ∸ r) -> (p + r == q)
    introduce-∸-≤ : {p q r : ℕ} -> (r ≤ q) -> (p + r ≤ q) -> (p ≤ q ∸ r)
    eliminate-∸-≤ : {p q r : ℕ} -> (r ≤ q) -> (p ≤ q ∸ r) -> (p + r ≤ q)
    introduce-∸-≤l : {p q r : ℕ} -> (r ≤ p) -> (p ≤ q + r) -> (p ∸ r ≤ q)
    eliminate-∸-≤l : {p q r : ℕ} -> (r ≤ p) -> (p ∸ r ≤ q) -> (p ≤ q + r)
    ∸-to-zero : {p q : ℕ} -> (p == q) -> (p ∸ q == 0)
    minus-plus : {p q : ℕ} -> {q ≤ p} -> p ∸ q + q == p
    ∸-down2 : {n r : ℕ} -> {r ≤ n} -> ((S n) ∸ (S r)) == n ∸ r
    ≤-up2-+ : {p q r : ℕ} -> (p ≤ q) -> (r + p ≤ r + q)
    ≤-up2-r-+ : {p q r : ℕ} -> (p ≤ q) -> (p + r ≤ q + r)
    ≤-up-r-+ : {p q r : ℕ} -> (p ≤ q) -> (p ≤ q + r)
    ≤-up-+ : {p q r : ℕ} -> (p ≤ q) -> (p ≤ r + q)
    ≤-down-+ : {p q r : ℕ} -> (p + r ≤ q) -> (p ≤ q)
    ≡-down-+ : {p q r : ℕ} -> (r + p == r + q) -> (p == q)
    ≡-down-r-+ : {p q r : ℕ} -> (p + r == q + r) -> (p == q)
    ∸-anti-≤ : {p q r : ℕ} -> (q ≤ p) -> (p ≤ r) -> (r ∸ p) ≤ (r ∸ q)
    +-unit : {n : ℕ} -> n + 0 == n
    ≤-≡ : {n k : ℕ} -> (n ≤ k) -> (k ≤ n) -> (n == k)
    plus-minus : {p q : ℕ} -> (p ≤ q) -> p + (q ∸ p) == q

zero-∸ : (n : ℕ) -> (0 ∸ n == 0)
zero-∸ 0 = idp
zero-∸ (S n) = idp

∸-∸-+ : {p q r : ℕ} -> (r ≤ q) -> (q ≤ p + r) -> p ∸ (q ∸ r) == (p + r) ∸ q
∸-∸-+ {p} {O} {O} rq qpr = ! (+-unit-r p)
∸-∸-+ {p} {S q} {O} rq qpr = ! (ap (λ t -> t ∸ S q) ((+-unit-r p)))
∸-∸-+ {p} {O} {S r} rq qpr = ≤-abs rq
∸-∸-+ {p} {S q} {S r} (inl x) qpr = 
  let rec = ∸-∸-+ {p} {q} {r} (inl (≡-down2 x)) (≤-cancel-S (≤-trans qpr (transport (λ t -> t ≤ S (p + r)) (! (+-three-assoc {p} {1} {r})) ≤-refl)))
      lemma : (p + r) ∸ q == (p + S r) ∸ S q
      lemma = ap (λ x -> x ∸ S q) (! (+-three-assoc {p} {1} {r}))
  in rec ∙ lemma
∸-∸-+ {p} {S q} {S r} (inr x) qpr = 
  let rec = ∸-∸-+ {p} {q} {r} (inr (<-cancel-S x)) (≤-cancel-S (≤-trans qpr (transport (λ t -> t ≤ S (p + r)) (! (+-three-assoc {p} {1} {r})) ≤-refl)))
      lemma : (p + r) ∸ q == (p + S r) ∸ S q
      lemma = ap (λ x -> x ∸ S q) (! (+-three-assoc {p} {1} {r}))
  in rec ∙ lemma



∸-up : {n r : ℕ} -> (r < n) -> (n ∸ r) == S (n ∸ (S r))
∸-up {S n} {O} p = idp
∸-up {S O} {S r} (ltSR p) = ⊥-elim (S≰O r (inr p))
∸-up {S (S n)} {S .n} ltS = ∸-up {S n} {n} ltS
∸-up {S (S n)} {S r} (ltSR p) = ∸-up {S n} {r} (ltSR (<-cancel-S p))

nowhere : {n k : ℕ} -> (¬ (n < k)) -> (¬ (n == k)) -> (¬ (n == 1 + k)) -> (¬ (1 + k < n)) -> ⊥
nowhere {0} {0} p1 p2 p3 p4 = p2 idp
nowhere {0} {S k} p1 p2 p3 p4 = p1 (O<S k)
nowhere {S 0} {0} p1 p2 p3 p4 = p3 idp
nowhere {S (S n)} {0} p1 p2 p3 p4 = p4 (<-ap-S (O<S n))
nowhere {S n} {S k} p1 p2 p3 p4 = nowhere (λ x → p1 (<-ap-S x)) (λ x → p2 (ap S x)) (λ x → p3 (ap S x)) (λ x → p4 (<-ap-S x))

≤-≠-≤ : {n m : ℕ} -> (n ≤ S m) -> ¬ (n == S m) -> (n ≤ m)
≤-≠-≤ {O} {m} p q = O≤ m
≤-≠-≤ {S n} {O} (inl x) q = ⊥-elim (q x)
≤-≠-≤ {S n} {O} (inr (ltSR x)) q = inr x
≤-≠-≤ {S n} {S m} p q = ≤-ap-S (≤-≠-≤ {n} {m} (≤-cancel-S p) λ x → q (ap S x))

≤-∃ : (n m : ℕ) -> (n ≤ m) -> Σ ℕ (λ t -> t + n == m)
≤-∃ n m (inl x) = 0 , x
≤-∃ n .(S n) (inr ltS) = 1 , idp
≤-∃ n (S m) (inr (ltSR x)) = 
    let x = ≤-∃ n m (inr x)
    in  1 + x .fst , ap S (x .snd)

rrr : {k : ℕ} -> k ≤ k
rrr = inl idp
