{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.Coxeter1 where

open import lib.Basics
open import lib.types.Nat
open import lib.types.Fin
open import lib.types.Sigma
open import lib.types.List
open import lib.types.SetQuotient

-- _↓_ : (n : ) -> (k : ℕ) -> List ℕ
-- n ↓ 0 = nil
-- n ↓ (S k) = (k + n) :: (n ↓ k)

postulate
    C : ℕ → Type₀

module _ {n : ℕ} where
    infixr 30 _↓_::_

    postulate
        nilC : C n
        _↓_::_ : (k : Fin n) -> (l : ℕ) → C n → C n
        
        cancel : ∀ (x : Fin n) -> (xs : C n) → xs == (x ↓ 1 :: (x ↓ 1  :: xs))
        swap : ∀ (x y : Fin n) -> (zs : C n) → (S (x .fst) < y .fst) → (y ↓ 1 :: (x ↓ 1 :: zs)) == (x ↓ 1 :: (y ↓ 1 :: zs))
        -- long : ∀ x y zs → (x ↓ (S y) :: ((S x) ↓ 1 :: zs)) == (x ↓ 1 :: (x ↓ S y :: zs))
        join: (a ↓ b) :: (a + b + 1 ↓ c) == (a ↓ c)

        trunc : is-set (C n)


    module CElim {i} {P : C n -> Type i}
        (nilC* : P nilC)
        (consC* : (k : Fin n) -> (l : ℕ) -> {c : C n} -> (p : P c) -> P (k ↓ l :: c))
        (cancel* : (x : Fin n) -> {xs : C n} -> (xs* : P xs) -> xs* == consC* x 1  (consC* x (1) xs*) [ P ↓ (cancel x xs) ]) where
        postulate
            f : (c : C n) -> P c
            f-nilC-β : f nilC ↦ nilC*
            f-consC-β : (k : Fin n) (l : ℕ) (xs : C n) -> f (k ↓ l :: xs) ↦ consC* k l (f xs)
            {-# REWRITE f-nilC-β #-}
            {-# REWRITE f-consC-β #-}
        postulate
            f-cancel-β : (x : Fin n) -> (xs : C n) -> apd f (cancel x xs) == cancel* x (f xs)

    module CRec {i} {P : Type i}
        (nilC* : P) (consC* : (k : Fin n) -> (l : ℕ) -> P -> P)
        (cancel* : (x : Fin n) (xs : P) -> xs == consC* x 1  (consC* x 1 xs)) where

        private module CE = CElim {P = λ _ -> P} 
                        nilC*
                        (λ k l p → consC* k l p) 
                        (λ x {xs} xs* → ↓-cst-in (cancel* x xs*))

        f : C n -> P
        f = CE.f


data D : ℕ → Type₀ where
    nilD : {n : ℕ} -> D n
    _↑_::_ : {n : ℕ} -> (k : ℕ) -> (n < k) -> (l : Fin k) → D n → D k

f : {n : ℕ} -> (c : C n) -> Σ (D n) (λ d → immersion d == c)

f : {n : ℕ} -> C n -> D n
f = fst (CRec.f {!   !} {!   !} {!   !} {!   !})


-- ∀ (x : Fin n) (xs : C n) -> f xs == f (_↓_::_ x (1 , {!   !}) {{!   !}} (_↓_::_ x (1 , {!   !}) {{!   !}} xs))

-- g : {n : ℕ} -> D n -> C n






-- -- TODO is it important for isCanonical to be a Prop
-- data isCanonical {n : ℕ} : C n -> Set where
--     base : isCanonical nilC
--     ind : (y1 x1 y2 x2 : Fin n) -> (l : C n) -> (((y2 .fst) + (x2 .fst)) < ((y1 .fst) + (x1 .fst)))
--         -> isCanonical (x2 ↓ y2 :: l) -> isCanonical (x1 ↓ y1 :: (x2 ↓ y2 :: l))

-- Canonical : ℕ -> Type₀
-- Canonical n = Σ (C n) isCanonical

-- Code : {n : ℕ} -> (xs ys : C n) -> Set -- xs ≃ ys (Prop?)
-- encode : {n : ℕ} -> (xs ys : C n) -> (p : xs == ys) -> Code xs ys
-- decode : {n : ℕ} -> (xs ys : C n) -> Code xs ys -> (xs == ys)

-- data piecewise-eq {n : ℕ} : C n -> C n -> Set where
--     ↓≡ : piecewise-eq nilC nilC
--     ::≡ : (a b : Fin n) -> (l1 l2 : C n) -> piecewise-eq l1 l2 -> piecewise-eq (a ↓ b :: l1) (a ↓ b :: l2)

-- lemmaleft : {n : ℕ} -> (xs ys : C n) -> isCanonical xs -> isCanonical ys -> xs == ys -> piecewise-eq xs ys

-- lemmaright : {n : ℕ} -> (xs ys : C n) -> isCanonical xs -> isCanonical ys -> piecewise-eq xs ys -> xs == ys

-- roundtrip : 

-- -- lemma : (x x' : C n) -> isCanonical x -> isCanonical x' -> 
-- --     (x1 ↓ y1) :: (x2 ↓ y2) ::(x3 ↓ y3) ... (xn ↓ yn) == (x1' ↓ y1') :: (x2' ↓ y2') ::(x3' ↓ y3') ... (xn' ↓ yn')
-- --     -> x1 == x1' × y1 == y1' × x2 == x2' ...


-- -- (x : Lehmer n) -> c->l (l->c x) == x

-- data Lehmer : ℕ -> Type₀ where


-- canonicalLehmer : ∀ n → Canonical n ≃ Lehmer n

-- everythingIsCanonical : ∀ n -> (xs : C n) -> Σ _ (λ ys -> ((isCanonical ys) × (ys == xs)))
-- CisCanonical : ∀ n -> C n ≃ Canonical n
-- finalLemma : ∀ n → C n ≃ Lehmer n