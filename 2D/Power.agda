{-# OPTIONS --without-K #-}

module 2D.Power where

open import Data.Nat using (ℕ; suc)
open import Data.Integer as ℤ
open import Relation.Binary.PropositionalEquality using (_≡_; subst; refl)

open import 2D.Types

infix 40 _^_

_^_ : {τ : U} → (p : τ ⟷ τ) → (k : ℤ) → (τ ⟷ τ)
p ^ (+ 0) = Prim id⟷
p ^ (+ (suc k)) = p ◎ (p ^ (+ k))
p ^ -[1+ 0 ] = ! p
p ^ (-[1+ (suc k) ]) = (! p) ◎ (p ^ -[1+ k ])

assoc1 : {τ : U} → {p : τ ⟷ τ} → (m : ℕ) →
  (p ◎ (p ^ (+ m))) ⇔ ((p ^ (+ m)) ◎ p)
assoc1 ℕ.zero = idr◎l ● idl◎r
assoc1 (suc m) = (id⇔ ⊡ assoc1 m) ● assoc◎l

assoc1- : {τ : U} → {p : τ ⟷ τ} → (m : ℕ) →
  ((! p) ◎ (p ^ -[1+ m ])) ⇔ ((p ^ -[1+ m ]) ◎ (! p))
assoc1- ℕ.zero = id⇔
assoc1- (suc m) = (id⇔ ⊡ assoc1- m) ● assoc◎l

lower : {τ : U} {p : τ ⟷ τ} (m n : ℤ) → p ^ (m ℤ.+ n) ⇔ ((p ^ m) ◎ (p ^ n))
lower (+_ ℕ.zero) (+_ n) = idl◎r
lower (+_ ℕ.zero) (-[1+_] n) = idl◎r
lower (+_ (suc m)) (+_ n) = (id⇔ ⊡ lower (+ m) (+ n)) ● assoc◎l
lower {p = p} (+_ (suc m)) (-[1+_] ℕ.zero) =
  idr◎r ● (id⇔ ⊡ linv◎r) ● assoc◎l ● (2! (assoc1 m) ⊡ id⇔)
lower (+_ (suc m)) (-[1+_] (suc n)) = -- p ^ ((m + 1) -(1+1+n)
  (lower (+ m) (-[1+ n ])) ● idr◎r ⊡ id⇔ ● ((id⇔ ⊡ linv◎r)  ⊡ id⇔) ●
  assoc◎r ● (id⇔ ⊡ assoc◎r) ● assoc◎l ● (2! (assoc1 m) ⊡ id⇔)
lower (-[1+_] m) (+_ ℕ.zero) = idr◎r
lower (-[1+_] ℕ.zero) (+_ (suc n)) = 2! (assoc◎l ● (rinv◎l ⊡ id⇔) ● idl◎l)
lower (-[1+_] (suc m)) (+_ (suc n)) = -- p ^ (-(1+m) + (n+1))
  lower (-[1+ m ]) (+ n) ● idr◎r ⊡ id⇔ ● ((id⇔ ⊡ rinv◎r)  ⊡ id⇔) ●
  assoc◎r ● (id⇔ ⊡ assoc◎r) ● assoc◎l ● (2! (assoc1- m) ⊡ id⇔)
lower (-[1+_] ℕ.zero) (-[1+_] n) = id⇔
lower (-[1+_] (suc m)) (-[1+_] n) = -- p ^ (-(1+1+m) - (1+n))
  (id⇔ ⊡ lower (-[1+ m ]) (-[1+ n ])) ● assoc◎l

-- more generally
assoc1g : {τ : U} → {p : τ ⟷ τ} → (i : ℤ) →  (p ◎ (p ^ i)) ⇔ ((p ^ i) ◎ p)
assoc1g (+_ n) = assoc1 n
assoc1g (-[1+_] ℕ.zero) = linv◎l ● rinv◎r
assoc1g (-[1+_] (suc n)) = assoc◎l ● linv◎l ⊡ id⇔ ● idl◎l ●
  (2! (assoc1- n ⊡ id⇔ ● assoc◎r ● id⇔ ⊡ rinv◎l ● idr◎l))

open import Data.Integer.Properties renaming (commutativeRing to ℤcr)
open import Algebra
open import Algebra.Structures

-- and even more generally.  Could do proof without subst, but this is simpler.
comm-i-j : {τ : U} → {p : τ ⟷ τ} → (i j : ℤ) →  ((p ^ i ) ◎ (p ^ j)) ⇔ ((p ^ j) ◎ (p ^ i))
comm-i-j {_} {p} i j =
  2! (lower i j) ● subst (λ k → p ^ (i ℤ.+ j) ⇔ p ^ k) (+-comm i j) (id⇔ {c = p ^ (i ℤ.+ j)}) ●
  lower j i
  where
    module cr = CommutativeRing ℤcr
    open cr

^⇔! : {τ : U} → {p : τ ⟷ τ} → (k : ℤ) → (p ^ (ℤ.- k)) ⇔ ! (p ^ k)
^⇔! (+_ ℕ.zero) = id⇔
-- need to dig deeper, as we end up negating
^⇔! (+_ (suc ℕ.zero)) = idl◎r
^⇔! (+_ (suc (suc n))) = assoc1- n ● ^⇔! (+ ℕ.suc n) ⊡ id⇔
^⇔! {p = p} (-[1+_] ℕ.zero) = idr◎l ● !!⇔id p
^⇔! {p = p} (-[1+_] (suc n)) =
  assoc1 (ℕ.suc n) ● (^⇔! -[1+ n ]) ⊡ (!!⇔id p)

id^i⇔id : {τ : U} (i : ℤ) → (Prim (id⟷ {τ})) ^ i ⇔ (Prim id⟷)
id^i⇔id (+_ ℕ.zero) = id⇔
id^i⇔id (+_ (ℕ.suc n)) = idl◎l ● id^i⇔id (+ n)
id^i⇔id (-[1+_] ℕ.zero) = id⇔
id^i⇔id (-[1+_] (ℕ.suc n)) = idl◎l ● id^i⇔id -[1+ n ]

eq-power : {τ : U} {p : τ ⟷ τ} → {i j : ℤ} → i ≡ j → p ^ i ⇔ p ^ j
eq-power refl = id⇔
