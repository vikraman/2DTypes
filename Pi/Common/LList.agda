{-# OPTIONS --without-K --rewriting #-}

module Pi.Common.LList where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.NType
open import lib.PathGroupoid
open import lib.Equivalence
open import lib.PathOver
open import lib.types.Fin

open import Pi.Common.Arithmetic
open import Pi.Common.ListN
open import Pi.Common.InequalityEquiv

data _>>_ : ℕ -> Listℕ -> Type₀ where
  nil : {n : ℕ} -> n >> nil
  _:⟨_⟩:_ : {n : ℕ} -> {l : Listℕ} -> (k : ℕ) -> (k < n) -> n >> l -> n >> (k ∷ l)

extract-proof : {n : ℕ} -> {l : Listℕ} -> {a : ℕ} -> (n >> (a ∷ l)) -> (a < n)
extract-proof (_ :⟨ p ⟩: _) = p

>>-↓ : (n k r : ℕ) -> (r + k ≤ n) -> (n >> (k ↓ r))
>>-↓ n k 0 p = nil
>>-↓ n k (S r) p = (r + k) :⟨ p ⟩: (>>-↓ n k r (≤-down p))

>>-++ : {n : ℕ} -> {l1 l2 : Listℕ} -> n >> l1 -> n >> l2 -> n >> (l1 ++ l2)
>>-++ {n} {nil} {l2} ll1 ll2 = ll2
>>-++ {n} {x ∷ l1} {l2} (.x :⟨ p ⟩: ll1) ll2 = x :⟨ p ⟩: (>>-++ ll1 ll2)

>>-S : {n : ℕ} -> {l : Listℕ} -> (n >> l) -> ((S n) >> l)
>>-S  nil = nil
>>-S  (k :⟨ p ⟩: l') = k :⟨ ≤-up p ⟩: >>-S l'

>>-rev : {n : ℕ} -> {l : Listℕ} -> (n >> l) -> (n >> rev l)
>>-rev {n} nil = nil
>>-rev {n} (k :⟨ x ⟩: lp) = >>-++ (>>-rev lp) (k :⟨ x ⟩: nil)

LList : ℕ → Type₀
LList n = Σ _ (λ l → n >> l)

>>-implies-> : {n a : ℕ} -> {l l1 r1 : Listℕ} -> (n >> l) -> (l == l1 ++ a ∷ r1) -> (a < n)
>>-implies-> {n} {l = .(k ∷ _)} {nil} {r1} (k :⟨ x ⟩: nl) p = transport (λ e -> e < n) (cut-tail p) x
>>-implies-> {n} {l = x₁ ∷ l} {x ∷ l1} {r1} (_ :⟨ _ ⟩: nl) p = >>-implies-> nl (cut-head p)

>>-implies->> : {n : ℕ} -> {l l1 m1 r1 : Listℕ} -> (n >> l) -> (l == l1 ++ (m1 ++ r1)) -> n >> m1
>>-implies->> {l = l} {l1 = nil} {m1 = nil} nl p = nil
>>-implies->> {n} {l = .(k ∷ _)} {l1 = nil} {m1 = x ∷ m1} (k :⟨ x₁ ⟩: nl) p = 
  x :⟨ transport (λ e -> e < n) (cut-tail p) x₁ ⟩: >>-implies->> {_} {_} {nil} {m1} {_} nl (cut-head p)
>>-implies->> {l = x₁ ∷ l} {l1 = x ∷ l1} {m1 = m1} (.x₁ :⟨ x₂ ⟩: nl) p = >>-implies->> {_} {l} {l1} {m1} nl (cut-head p)

-- _:⟨⟩:_ : {m : ℕ} -> Fin m -> LList m -> LList m
-- (x , xp) :⟨⟩: (xs , xsp) = (x ∷ xs) , (x :⟨ –> <N≃< xp ⟩: xsp)

head+tail>> : {n a : ℕ} -> (ap1 : a < n) -> (ap2 : a < n) -> {l : Listℕ} -> {lp1 : n >> l} -> {lp2 : n >> l} -> (lp1 == lp2) -> (a :⟨ ap1 ⟩: lp1) == (a :⟨ ap2 ⟩: lp2)
head+tail>> {a = a} ap1 ap2 {lp1 = lp1} {lp2 = lp2} pl = ap (λ e -> (a :⟨ ap1 ⟩: e)) pl ∙ ap (λ e -> a :⟨ e ⟩: lp2) (≤-has-all-paths ap1 ap2)

>>-eq : {n : ℕ} -> {l : Listℕ} -> (lp1 : n >> l) -> (lp2 : n >> l) -> (lp1 == lp2)
>>-eq nil nil = idp
>>-eq (k :⟨ kp1 ⟩: lp1) (.k :⟨ kp2 ⟩: lp2) = head+tail>> kp1 kp2 (>>-eq lp1 lp2)

>>-eq-d : {n : ℕ} -> {l1 l2 : Listℕ} -> (p : l1 == l2) -> (lp1 : n >> l1) -> (lp2 : n >> l2) -> PathOver (_>>_ n) p lp1 lp2
>>-eq-d {n} idp lp1 lp2 = >>-eq lp1 lp2

LList-eq : {n : ℕ} -> {l1 l2 : LList n} -> ((l1 .fst) == (l2 .fst)) -> (l1 == l2)
LList-eq {n} {l1} {l2} p = pair= p (>>-eq-d p (l1 .snd) (l2 .snd))

LList-rev : {n : ℕ} -> (l1 : LList n) -> LList n
LList-rev (l , lp) = (rev l) , (>>-rev lp)