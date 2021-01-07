{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Arithmetic where

open import lib.Base
open import lib.types.Nat using (_+_ ; ℕ-S-is-inj)
open import lib.PathGroupoid
open import lib.NType
open import Pi+.Misc

infix 4 _≤_ _<_

data _≤_ : ℕ -> ℕ -> Type₀ where
  z≤n : ∀ {n}                 → 0  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → S m ≤ S n

≤-has-all-paths : {m n : ℕ} -> (p : m ≤ n) -> (q : m ≤ n) -> p == q
≤-has-all-paths {O} {O} z≤n z≤n = idp
≤-has-all-paths {O} {S n} z≤n z≤n = idp
≤-has-all-paths {S m} {S n} (s≤s p) (s≤s q) = 
  let rec = ≤-has-all-paths p q 
  in  ap s≤s rec

instance
  ≤-level : {m n : ℕ} → is-prop (m ≤ n)
  ≤-level = all-paths-is-prop ≤-has-all-paths

_<_ : ℕ -> ℕ -> Type₀
m < n = S m ≤ n

≤-trans : {m n r : ℕ} -> m ≤ n -> n ≤ r -> m ≤ r
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)

≤-reflexive : {p q : ℕ} -> p == q -> p ≤ q
≤-reflexive {0}  idp = z≤n
≤-reflexive {S m} idp = s≤s (≤-reflexive idp)

≤-up : {n m : ℕ} -> m ≤ n -> m ≤ S n
≤-up {n} {.0} z≤n = z≤n
≤-up {.(S _)} {.(S _)} (s≤s q) = s≤s (≤-up q)

≤-up2 : {n m : ℕ} -> m ≤ n -> S m ≤ S n
≤-up2 p = s≤s p

≤-down : {n m : ℕ} -> S m ≤ n -> m ≤ n
≤-down {.(S _)} {0} (s≤s p) = z≤n
≤-down {.(S _)} {S n} (s≤s p) = s≤s (≤-down p)

≤-down2 : {n m : ℕ} -> S m ≤ S n -> m ≤ n
≤-down2 {m} {n} (s≤s p) = p

≤-abs : {A : Type₀} -> {n : ℕ} -> (S n ≤ 0) -> A
≤-abs ()

1+n≰n : ∀ {n} → ¬ (1 + n ≤ n)
1+n≰n (s≤s le) = 1+n≰n le

abs-refl : {A : Type₀} -> {n : ℕ} -> n < n -> A
abs-refl p = ⊥-elim (1+n≰n p)

abs-suc : {A : Type₀} -> {n : ℕ} -> S n < n -> A
abs-suc {n} p = ⊥-elim (1+n≰n (≤-down p))

+-unit : {n : ℕ} -> n + 0 == n
+-unit {O} = idp
+-unit {S n} = ap S +-unit

+-S : ∀ m n → m + S n == S (m + n)
+-S 0    n = idp
+-S (S m) n = cong S (+-S m n)

+-comm : (m n : ℕ) -> (m + n) == (n + m)
+-comm O n = ! +-unit
+-comm (S m) n =
  begin
  S m + n   =⟨ idp ⟩
  S (m + n) =⟨ cong S (+-comm m n) ⟩
  S (n + m) =⟨ ≡-sym (+-S n m) ⟩
  n + S m   =∎

+-assoc : (m n r : ℕ) -> (m + n) + r == m + (n + r)
+-assoc 0    _ _ = idp
+-assoc (S m) n o = cong S (+-assoc m n o)

infixl 81 _∸_
_∸_ : ℕ → ℕ → ℕ
m ∸ 0   =  m
0 ∸ S n  =  0
S m ∸ S n  =  m ∸ n

≡-down2 : {p q : ℕ} -> (S p == S q) -> p == q   
≡-down2 {p} {q} r = ℕ-S-is-inj p q r


_≤?_ : (n m : ℕ) -> BoolDec (n ≤ m)
O ≤? m = yes z≤n
S n ≤? O = no (λ ())
S n ≤? S m with n ≤? m
... | yes p = yes (s≤s p)
... | no  q = no (λ x → q (≤-down2 x))

_<?_ : (n m : ℕ) -> BoolDec ((S n) ≤ m)
n <? m = (S n) ≤? m

_≟_ : (n m : ℕ) -> BoolDec (n == m)
O ≟ O = yes idp
O ≟ S m = no (λ ())
S n ≟ O = no (λ ())
S n ≟ S m with n ≟ m
... | yes p = yes (ap S p)
... | no  p = no (λ x → p (≡-down2 x))


postulate
    ∸-implies-≤ : {p q r : ℕ} -> (p == q ∸ r) -> (p ≤ q)
    ≤-remove-+ : {p q r : ℕ} -> (p + q ≤ r) -> (q ≤ r)
    introduce-≤-from-+ : {p q r : ℕ} -> (p + q == r) -> (p ≤ r)
    +-three-assoc : {k i r : ℕ} -> k + (i + r) == (i + k) + r
    introduce-∸ : {p q r : ℕ} -> (r ≤ q) -> (p + r == q) -> (p == q ∸ r)
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
    ≤-≡ : {n k : ℕ} -> (n ≤ k) -> (k ≤ n) -> (n == k)
    plus-minus : {p q : ℕ} -> (p ≤ q) -> p + (q ∸ p) == q

zero-∸ : (n : ℕ) -> (0 ∸ n == 0)
zero-∸ 0 = idp
zero-∸ (S n) = idp

∸-anti-≤ : {p q r : ℕ} -> (q ≤ p) -> (r ∸ p) ≤ (r ∸ q)
∸-anti-≤ {p} {.0} {r} z≤n = ∸-implies-≤ {r ∸ p} {r} {p} idp
∸-anti-≤ {S p} {S q} {O} (s≤s qp) = z≤n
∸-anti-≤ {S p} {S q} {S r} (s≤s qp) = ∸-anti-≤ {p} {q} {r} qp

≰⇒> : {m n : ℕ} -> ¬ (m ≤ n) -> n < m
≰⇒> {O} {n} p = ⊥-elim (p z≤n)
≰⇒> {S m} {O} p = s≤s z≤n
≰⇒> {S m} {S n} p = 
  let rec = ≰⇒> {m} {n} (λ x → p (s≤s x))
  in  s≤s rec

∸-∸-+ : {p q r : ℕ} -> (r ≤ q) -> (q ≤ p + r) -> p ∸ (q ∸ r) == (p + r) ∸ q
∸-∸-+ {p} {0} {0} rq qpr = +-comm 0 p
∸-∸-+ {p} {S q} {0} rq qpr rewrite +-comm p 0 = idp
∸-∸-+ {p} {S q} {S r} (s≤s rq) qpr =
  let rec = ∸-∸-+ {p} {q} {r} rq (≤-down2 (≤-trans qpr (≤-reflexive (+-three-assoc {p} {1} {r}))))
      lemma : (p + r) ∸ q == (p + S r) ∸ S q
      lemma = cong (λ x -> x ∸ S q) (≡-sym (+-three-assoc {p} {1} {r}))
  in ≡-trans rec lemma

∸-up : {n r : ℕ} -> (r < n) -> (n ∸ r) == S (n ∸ (S r))
∸-up {S 0} {0} p = idp
∸-up {S 0} {S r} (s≤s p) = ≤-abs p
∸-up {S (S n)} {0} p = idp
∸-up {S (S n)} {S r} (s≤s p) = ∸-up {S n} {r} p

nowhere : {n k : ℕ} -> (¬ (n < k)) -> (¬ (n == k)) -> (¬ (n == 1 + k)) -> (¬ (1 + k < n)) -> ⊥
nowhere {0} {0} p1 p2 p3 p4 = p2 idp
nowhere {0} {S k} p1 p2 p3 p4 = p1 (s≤s z≤n)
nowhere {S 0} {0} p1 p2 p3 p4 = p3 idp
nowhere {S (S n)} {0} p1 p2 p3 p4 = p4 (s≤s (s≤s z≤n))
nowhere {S n} {S k} p1 p2 p3 p4 = nowhere (λ x → p1 (s≤s x)) (λ x → p2 (cong S x)) (λ x → p3 (cong S x)) (λ x → p4 (s≤s x))

≤-≠-≤ : {n m : ℕ} -> (n ≤ S m) -> ¬ (n == S m) -> (n ≤ m)
≤-≠-≤ {0} {0} p q = z≤n
≤-≠-≤ {0} {S m} p q = z≤n
≤-≠-≤ {S 0} {0} p q = ⊥-elim (q idp)
≤-≠-≤ {S (S n)} {0} (s≤s ()) q
≤-≠-≤ {S n} {S m} (s≤s p) q = s≤s (≤-≠-≤ p λ x → q (cong S x))

≤-∃ : (n m : ℕ) -> (n ≤ m) -> Σ ℕ (λ t -> t + n == m)
≤-∃ .0 m z≤n = m , +-unit
≤-∃ (S n) (S m) (s≤s p) =
  let rec-t , rec-p = ≤-∃ n m p
  in  rec-t , ≡-trans (+-three-assoc {rec-t} {1} {n}) (cong S rec-p)

rrr : {k : ℕ} -> k ≤ k
rrr = ≤-reflexive idp

squeeze : {n k : ℕ} -> (n < k) -> (k ≤ S n) -> (k == S n)
squeeze {.0} {.1} (s≤s {n = .0} z≤n) (s≤s z≤n) = idp
squeeze {.(S _)} {.(S (S _))} (s≤s (s≤s pn)) (s≤s (s≤s pnn)) = ap S (squeeze (s≤s pn) (s≤s pnn))


module ≤-Reasoning where
    infix  1 ≤begin_
    infixr 2 _≤⟨⟩_ _≤⟨_⟩_ _≡⟨⟩_ _≡⟨_⟩_
    infix  3 _≤∎

    ≤begin_ : ∀ {x y : ℕ}
             → x ≤ y
               -----
             → x ≤ y
    ≤begin x≤y  =  x≤y

    _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
            → x ≤ y
              -----
            → x ≤ y
    x ≤⟨⟩ x≤y  =  x≤y

    _≡⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
            → x == y
              -----
            → x ≤ y
    x ≡⟨⟩ x≡y  = ≤-reflexive x≡y

    _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
             → x ≤ y
             → y ≤ z
               -----
             → x ≤ z
    x ≤⟨ x≤y ⟩ y≤z  = ≤-trans x≤y y≤z

    _≡⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
             → x == y
             → y ≤ z
               -----
             → x ≤ z
    x ≡⟨ x≡y ⟩ y≤z  = ≤-trans (≤-reflexive x≡y) y≤z

    _≤∎ : ∀ (x : ℕ)
           -----
          → x ≤ x
    x ≤∎  = ≤-reflexive idp
