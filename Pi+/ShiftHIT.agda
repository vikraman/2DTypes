{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.Coxeter1 where

open import lib.Basics
open import lib.types.Nat
open import lib.types.Fin
open import lib.types.Sigma
open import lib.types.List
open import lib.types.SetQuotient


-- This HIT forms a presentation of S_n in which generators consist of shifts (of the form: [a ↓ b]).
-- A shift [a ↓ b] represents moving a-th element of a list b places right, shifting everything else to the left
-- For example, we have a list    X = [1,2,3,4,5,6,7,8,9] and a shift τ₀ = 3 ↓ 4
-- Then, τ₀ acting on X produces τ₀ X = [1,2,4,5,6,7,3,8,9]
-- For each τ , we can interpret it in as a list of adjacent transpositions:
-- In our case, τ₀ = (3 4) (4 5) (5 6) (6 7)
-- so in general τ = [a ↓ b] is interpreted as (a a+1) (a+1 a+2) ... (a+b-1 a+b)
-- Using this homomorphism on generators, out of the set of relations on Coxeter presentation, 
-- we can get a set of relations on shift- presentation.
-- The relations are written below. (some of them are commented out since we didn't finish writing elimination principles for them)

postulate
    C : ℕ → Type₀

module _ {n : ℕ} where
    infixr 30 _↓_::_

    postulate
        nilC : C n
        _↓_::_ : (k : Fin n) -> (l : ℕ) → C n → C n
        
        cancel : ∀ (x : Fin n) -> (xs : C n) → xs == (x ↓ 1 :: (x ↓ 1  :: xs))
        -- swap : ∀ (x y : Fin n) -> (zs : C n) → (S (x .fst) < y .fst) → (y ↓ 1 :: (x ↓ 1 :: zs)) == (x ↓ 1 :: (y ↓ 1 :: zs))
        -- long : ∀ x y zs → (x ↓ (S y) :: ((S x) ↓ 1 :: zs)) == (x ↓ 1 :: (x ↓ S y :: zs))
        -- join: (a ↓ b) :: (a + b + 1 ↓ c) == (a ↓ c)

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