{-# OPTIONS --without-K --rewriting #-}

module Pi+.CoxeterCommon.ListN where

open import lib.Base
open import lib.PathGroupoid
open import lib.types.Nat using (_+_)
open import lib.Function
open import Pi+.CoxeterCommon.Arithmetic
open import Pi+.Misc

infixr 35 _::_

data Listℕ : Type₀ where
  nil : Listℕ
  _::_ : ℕ → Listℕ → Listℕ

infixr 34 _++_

_++_ : Listℕ → Listℕ → Listℕ
nil ++ l = l
(x :: l₁) ++ l₂ = x :: (l₁ ++ l₂)

reverse : Listℕ -> Listℕ
reverse nil = nil
reverse (x :: xs) = (reverse xs) ++ (x :: nil)

++-unit-r : ∀ l → l ++ nil == l
++-unit-r nil      = idp
++-unit-r (a :: l) = ap (a ::_) $ ++-unit-r l

++-assoc : ∀ l₁ l₂ l₃ → (l₁ ++ l₂) ++ l₃ == l₁ ++ (l₂ ++ l₃)
++-assoc nil l₂ l₃ = idp
++-assoc (x :: l₁) l₂ l₃ = ap (x ::_) (++-assoc l₁ l₂ l₃)

++-assoc-≡ : {l r1 r2 m : Listℕ} -> m == ((l ++ r1) ++ r2) -> m == (l ++ (r1 ++ r2))
++-assoc-≡ {l} {r1} {r2} {m} p = ≡-trans p (++-assoc l r1 r2)

reverse-++-commute : (xs ys : Listℕ) → reverse (xs ++ ys) == reverse ys ++ reverse xs
reverse-++-commute nil ys = ! (++-unit-r (reverse ys))
reverse-++-commute (x :: xs) ys = 
  let rec = reverse-++-commute xs ys
  in  ap (λ t -> t ++ x :: nil) rec ∙ ++-assoc (reverse ys) (reverse xs) (x :: nil)

infixr 60 _↓_

_↓_ : (n : ℕ) -> (k : ℕ) -> Listℕ
n ↓ 0 = nil
n ↓ (S k) = (k + n) :: (n ↓ k)

[_] : ℕ -> Listℕ
[ x ] = x :: nil

++-unit : {l : Listℕ} -> l ++ nil == l
++-unit {nil} = idp
++-unit {x :: l} rewrite (++-unit {l}) = idp

cut-head : {a1 a2 : ℕ} -> {l1 l2 : Listℕ} -> (a1 :: l1) == (a2 :: l2) -> l1 == l2
cut-head {a1} {a2} {l1} {.l1} idp = idp

cut-tail : {a1 a2 : ℕ} -> {l1 l2 : Listℕ} -> (a1 :: l1 == a2 :: l2) -> (a1 == a2)
cut-tail {a1} {.a1} {l1} {.l1} idp = idp

cut-t1 : {a1 a2 : ℕ} -> {l1 l2 : Listℕ} -> (a1 :: l1 == a2 :: l2) -> (a1 == a2)
cut-t1 {a1} {.a1} {l1} {.l1} idp = idp

cut-t2 : {a1 a2 b1 b2 : ℕ} -> {l1 l2 : Listℕ} -> (a1 :: b1 :: l1 == a2 :: b2 :: l2) -> (b1 == b2)
cut-t2 {l1 = l1} {l2 = .l1} idp = idp

cut-t3 : {a1 a2 b1 b2 c1 c2 : ℕ} -> {l1 l2 : Listℕ} -> (a1 :: b1 :: c1 :: l1 == a2 :: b2 :: c2 :: l2) -> (c1 == c2)
cut-t3 {l1 = l1} {l2 = .l1} idp = idp

cut-t4 : {a1 a2 b1 b2 c1 c2 d1 d2 : ℕ} -> {l1 l2 : Listℕ} -> (a1 :: b1 :: c1 :: d1 :: l1 == a2 :: b2 :: c2 :: d2 :: l2) -> (d1 == d2)
cut-t4 {l1 = l1} {l2 = .l1} idp = idp

cut-h2 : {a1 a2 b1 b2 : ℕ} -> {l1 l2 : Listℕ} -> (a1 :: b1 :: l1 == a2 :: b2 :: l2) -> (l1 == l2)
cut-h2 {l1 = l1} {l2 = .l1} idp = idp

cut-h3 : {a1 a2 b1 b2 c1 c2 : ℕ} -> {l1 l2 : Listℕ} -> (a1 :: b1 :: c1 :: l1 == a2 :: b2 :: c2 :: l2) -> (l1 == l2)
cut-h3 {l1 = l1} {l2 = .l1} idp = idp

cut-h4 : {a1 a2 b1 b2 c1 c2 d1 d2 : ℕ} -> {l1 l2 : Listℕ} -> (a1 :: b1 :: c1 :: d1 :: l1 == a2 :: b2 :: c2 :: d2 :: l2) -> (l1 == l2)
cut-h4 {l1 = l1} {l2 = .l1} idp = idp

head+tail : {h1 h2 : ℕ} -> {t1 t2 : Listℕ} -> (h1 == h2) -> (t1 == t2) -> (h1 :: t1) == (h2 :: t2)
head+tail idp idp = idp

start+end : {h1 h2 : Listℕ} -> {t1 t2 : Listℕ} -> (h1 == h2) -> (t1 == t2) -> (h1 ++ t1) == (h2 ++ t2)
start+end idp idp = idp

cut-last : {a1 a2 : ℕ} -> {l1 l2 : Listℕ} -> (l1 ++ [ a1 ] == l2 ++ [ a2 ]) -> (l1 == l2)
cut-last {a1} {.a1} {nil} {nil} idp = idp
cut-last {a1} {a2} {nil} {x :: nil} ()
cut-last {a1} {a2} {nil} {x :: x₁ :: l2} ()
cut-last {a1} {a2} {x :: nil} {nil} ()
cut-last {a1} {a2} {x :: x₁ :: l1} {nil} ()
cut-last {a1} {a2} {x :: l1} {x₁ :: l2} p = head+tail (cut-tail p) (cut-last (cut-head p))

cut-prefix : {a1 a2 : ℕ} -> {l1 l2 : Listℕ} -> (l1 ++ [ a1 ] == l2 ++ [ a2 ]) -> (a1 == a2)
cut-prefix {a1} {.a1} {nil} {nil} idp = idp
cut-prefix {a1} {a2} {nil} {x :: nil} ()
cut-prefix {a1} {a2} {nil} {x :: x₁ :: l2} ()
cut-prefix {a1} {a2} {x :: nil} {nil} ()
cut-prefix {a1} {a2} {x :: x₁ :: l1} {nil} ()
cut-prefix {a1} {a2} {x :: l1} {x₁ :: l2} p = cut-prefix (cut-head p)

↓-+ : (n k1 k2 : ℕ) -> (n ↓ (k1 + k2)) == ((n + k2) ↓ k1) ++ (n ↓ k2)
↓-+ n 0 k2 = idp
↓-+ n (S k1) k2 rewrite (↓-+ n k1 k2) rewrite (+-comm n k2) = head+tail ((+-assoc k1 k2 n)) idp

_↑_ : (n : ℕ) -> (k : ℕ) -> Listℕ
n ↑ 0 = nil
n ↑ (S k) = n :: (S n ↑ k)

++-↓ : (n k : ℕ) -> (((S n) ↓ k) ++ [ n ]) == (n ↓ (S k))
++-↓ n 0 = idp
++-↓ n (S k) rewrite ++-↓ n k = head+tail (+-three-assoc {k} {1} {n}) idp

++-↓-S : (n k x : ℕ) -> (S x == n) -> ((n ↓ k) ++ [ x ]) == (x ↓ (S k))
++-↓-S n O x p = idp
++-↓-S n (S k) x p rewrite (! p) rewrite ++-↓ n k = head+tail (+-three-assoc {k} {1} {x}) (++-↓ x k)

++-↑ : (n k : ℕ) -> ((n ↑ k) ++ [ k + n ]) == (n ↑ (S k))
++-↑ n 0 = idp
++-↑ n (S k) rewrite ≡-sym (++-↑ (S n) k) rewrite (+-three-assoc {k} {1} {n}) = idp

rev : Listℕ -> Listℕ
rev nil = nil
rev (x :: l) = (rev l) ++ [ x ]

rev-d : (k p : ℕ) -> (rev (k ↓ p)) == (k ↑ p)
rev-d k 0 = idp
rev-d k (S p) rewrite (rev-d k p) = ++-↑ k p

rev-u : (k p : ℕ) -> (rev (k ↑ p)) == (k ↓ p)
rev-u k 0 = idp
rev-u k (S p) rewrite (rev-u (S k) p) = ++-↓ k p

rev-++ : (l r : Listℕ) -> rev (l ++ r) == (rev r) ++ (rev l)
rev-++ nil r = ≡-sym ++-unit
rev-++ (x :: l) r =
  let rec = start+end (rev-++ l r) idp
  in  ≡-trans rec (++-assoc (rev r) (rev l) (x :: nil))

rev-rev : {l : Listℕ} -> l == rev (rev l)
rev-rev {nil} = idp
rev-rev {x :: l} = ≡-trans (head+tail idp (rev-rev {l})) (≡-sym (rev-++ (rev l) [ x ]))

telescope-rev : (n k : ℕ) -> (r : Listℕ) -> (((rev (S (S n) ↑ k) ++ S n :: nil) ++ n :: nil) ++ r) == ((n ↓ (2 + k)) ++ r)
telescope-rev n k r =
  begin
    ((rev (S (S n) ↑ k) ++ S n :: nil) ++ n :: nil) ++ r
  =⟨ start+end (start+end (start+end (rev-u (2 + n) k) idp) idp) idp ⟩
    (((S (S n) ↓ k) ++ S n :: nil) ++ n :: nil) ++ r
  =⟨ start+end (start+end (++-↓ (1 + n) k) idp) idp ⟩
    (((S n) ↓ (1 + k)) ++ n :: nil) ++ r
  =⟨ start+end (++-↓ n (1 + k)) idp ⟩
    (n ↓ (2 + k)) ++ r
  =∎

-- -- highly specific lemma...
telescope-l-rev-+1 : (n k : ℕ) -> (l r : Listℕ) -> ((((l ++ rev ((3 + n) ↑ k)) ++ (2 + n) :: nil) ++ (1 + n) :: nil) ++ n :: nil) ++ r == l ++ (n ↓ (3 + k)) ++ r
telescope-l-rev-+1 n k l r =
  begin
    ((((l ++ (rev ((S (S (S n)) ↑ k)))) ++ S (S n) :: nil) ++ S n :: nil) ++ n :: nil) ++ r
  =⟨ ++-assoc (((l ++ rev (S (S (S n)) ↑ k)) ++ S (S n) :: nil) ++ S n :: nil) (n :: nil) r ⟩
    _
  =⟨ ++-assoc ((l ++ rev (S (S (S n)) ↑ k)) ++ S (S n) :: nil) (S n :: nil) (n :: r) ⟩
    _
  =⟨ ++-assoc (l ++ rev (S (S (S n)) ↑ k)) (S (S n) :: nil) (S n :: n :: r) ⟩
    _
  =⟨ ++-assoc (l) (rev (S (S (S n)) ↑ k)) (S (S n) :: S n :: n :: r) ⟩
    l ++ (rev (S (S (S n)) ↑ k) ++ S (S n) :: S n :: n :: r)
  =⟨ start+end (idp {a = l}) (≡-sym (++-assoc (rev (S (S (S n)) ↑ k)) (S (S n) :: nil) _)) ⟩
    l ++ ((rev (S (S (S n)) ↑ k) ++ S (S n) :: nil) ++ S n :: n :: r)
  =⟨ start+end (idp {a = l}) (≡-sym (++-assoc (rev (S (S (S n)) ↑ k) ++ S (S n) :: nil) (S n :: nil) _)) ⟩
    l ++ (((rev (S (S (S n)) ↑ k) ++ S (S n) :: nil) ++ S n :: nil) ++ n :: r)
  =⟨ start+end (idp {a = l}) (≡-sym (++-assoc _ (n :: nil) r)) ⟩
    l ++ ((((rev (S (S (S n)) ↑ k) ++ S (S n) :: nil) ++ S n :: nil) ++ n :: nil) ++ r)
  =⟨ start+end (idp {a = l}) (start+end (telescope-rev (1 + n) k [ n ]) (idp {a = r})) ⟩
    l ++ ((((S n) ↓ (2 + k)) ++ n :: nil) ++ r)
  =⟨ start+end (idp {a = l}) (start+end (++-↓ n (S (S k))) (idp {a = r}))  ⟩
    _
  =∎

++-empty : (l r : Listℕ) -> (l ++ r) == l -> (r == nil)
++-empty nil r p = p
++-empty (x :: l) r p = ++-empty l r (cut-head p)

nil-abs : {x : ℕ} -> {l : Listℕ} -> (x :: l) == nil -> ⊥
nil-abs ()

++-abs : {x : ℕ} -> {l : Listℕ} -> l ++ [ x ] == nil -> ⊥
++-abs {x} {nil} ()
++-abs {x} {x₁ :: l} p = nil-abs p

++-abs-lr : {x : ℕ} -> {l r : Listℕ} -> l ++ x :: r == nil -> ⊥
++-abs-lr {x} {nil} ()
++-abs-lr {x} {x₁ :: l} p = nil-abs p

_↓↓_,_ : (n : ℕ) -> (k : ℕ) -> (k ≤ n) -> Listℕ
n ↓↓ 0 , z≤n = nil
S n ↓↓ S k , s≤s p = n :: (n ↓↓ k , p)

↓↓-↓ : (n : ℕ) -> (k : ℕ) -> (p : k ≤ k + n) -> (((k + n) ↓↓ k , p) == (n ↓ k))
↓↓-↓ n 0 z≤n = idp
↓↓-↓ n (S k) (s≤s p) rewrite (↓↓-↓ n k p) = idp

↓-↓↓ : (n : ℕ) -> (k : ℕ) -> (p : k ≤ n) -> (n ↓↓ k , p) == ((n ∸ k) ↓ k)
↓-↓↓ n 0 z≤n = idp
↓-↓↓ (S n) (S k) (s≤s p) rewrite (↓-↓↓ n k p) = head+tail (≡-sym (plus-minus p)) idp

-- ↓↓-rec : {n k : ℕ} -> (k < n) -> (n ↓↓ S k) == (n ↓↓ k) ++ [ n ∸ (k + 1) ]
-- ↓↓-rec {S 0} {0} (s≤s z≤n) = idp
-- ↓↓-rec {S (S n)} {0} (s≤s z≤n) = idp
-- ↓↓-rec {S (S n)} {S k} (s≤s p) = cong (λ l -> S n :: l) (↓↓-rec p)