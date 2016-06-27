module 2D.Power where

open import Data.Nat using (ℕ; suc)
open import Data.Integer as ℤ

open import 2D.Types

infix 40 _^_

_^_ : {τ : U} → (p : τ ⟷ τ) → (k : ℤ) → (τ ⟷ τ)
p ^ (+ 0) = Prim id⟷
p ^ (+ (suc k)) = p ◎ (p ^ (+ k))
p ^ -[1+ 0 ] = ! p
p ^ (-[1+ (suc k) ]) = (! p) ◎ (p ^ -[1+ k ])

assoc1 : {τ : U} → {p : τ ⟷ τ} → (m : ℕ) →
  (p ◎ (p ^ (+ m))) ⇔ ((p ^ (+ m)) ◎ p)
assoc1 ℕ.zero = trans⇔ idr◎l idl◎r
assoc1 (suc m) = trans⇔ (id⇔ ⊡ assoc1 m) assoc◎l

assoc1- : {τ : U} → {p : τ ⟷ τ} → (m : ℕ) →
  ((! p) ◎ (p ^ -[1+ m ])) ⇔ ((p ^ -[1+ m ]) ◎ (! p))
assoc1- ℕ.zero = id⇔
assoc1- (suc m) = trans⇔ (id⇔ ⊡ assoc1- m) assoc◎l

lower : {τ : U} {p : τ ⟷ τ} (m n : ℤ) → p ^ (m ℤ.+ n) ⇔ ((p ^ m) ◎ (p ^ n))
lower (+_ ℕ.zero) (+_ n) = idl◎r
lower (+_ ℕ.zero) (-[1+_] n) = idl◎r
lower (+_ (suc m)) (+_ n) = trans⇔ (id⇔ ⊡ lower (+ m) (+ n)) assoc◎l
lower {p = p} (+_ (suc m)) (-[1+_] ℕ.zero) =
  trans⇔ idr◎r (trans⇔ (id⇔ ⊡ linv◎r) (
  trans⇔ assoc◎l (2! (assoc1 m) ⊡ id⇔)))  -- p ^ ((m + 1) -1)
lower (+_ (suc m)) (-[1+_] (suc n)) = -- p ^ ((m + 1) -(1+1+n)
  trans⇔ (lower (+ m) (-[1+ n ])) (
  trans⇔ ((trans⇔ idr◎r (id⇔ ⊡ linv◎r))  ⊡ id⇔) (
  trans⇔ assoc◎r (trans⇔ (id⇔ ⊡ assoc◎r) (
  trans⇔ assoc◎l (2! (assoc1 m) ⊡ id⇔)))))
lower (-[1+_] m) (+_ ℕ.zero) = idr◎r
lower (-[1+_] ℕ.zero) (+_ (suc n)) = 2! (trans⇔ assoc◎l (
  trans⇔ (rinv◎l ⊡ id⇔) idl◎l))
lower (-[1+_] (suc m)) (+_ (suc n)) = -- p ^ (-(1+m) + (n+1))
  trans⇔ (lower (-[1+ m ]) (+ n)) (
    trans⇔ ((trans⇔ idr◎r (id⇔ ⊡ rinv◎r))  ⊡ id⇔) (
  trans⇔ assoc◎r (trans⇔ (id⇔ ⊡ assoc◎r) (
  trans⇔ assoc◎l ((2! (assoc1- m)) ⊡ id⇔)))))
lower (-[1+_] ℕ.zero) (-[1+_] n) = id⇔
lower (-[1+_] (suc m)) (-[1+_] n) = -- p ^ (-(1+1+m) - (1+n))
  trans⇔ (id⇔ ⊡ lower (-[1+ m ]) (-[1+ n ])) assoc◎l

^⇔! : {τ : U} → {p : τ ⟷ τ} → (k : ℤ) → (p ^ (ℤ.- k)) ⇔ ! (p ^ k)
^⇔! (+_ ℕ.zero) = id⇔
-- need to dig deeper, as we end up negating
^⇔! (+_ (suc ℕ.zero)) = idl◎r
^⇔! (+_ (suc (suc n))) = trans⇔ (assoc1- n) (^⇔! (+ ℕ.suc n) ⊡ id⇔)
^⇔! {p = p} (-[1+_] ℕ.zero) = trans⇔ idr◎l (!!⇔id p)
^⇔! {p = p} (-[1+_] (suc n)) =
  trans⇔ (assoc1 (ℕ.suc n)) ((^⇔! -[1+ n ]) ⊡ (!!⇔id p))

id^i⇔id : {τ : U} (i : ℤ) → (Prim (id⟷ {τ})) ^ i ⇔ (Prim id⟷)
id^i⇔id (+_ ℕ.zero) = id⇔
id^i⇔id (+_ (ℕ.suc n)) = trans⇔ idl◎l (id^i⇔id (+ n))
id^i⇔id (-[1+_] ℕ.zero) = id⇔
id^i⇔id (-[1+_] (ℕ.suc n)) = trans⇔ idl◎l (id^i⇔id -[1+ n ])
