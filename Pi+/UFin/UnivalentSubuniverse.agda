{-# OPTIONS --rewriting --without-K #-}

module Pi+.UFin.UnivalentSubuniverse where

open import HoTT

-- P : A -> U is a type family.
-- π_1 : Σ A P -> A is a fibration.

-- π_1 is univalent => transport : ((x , p) = (y , q) : Σ A P) -> (x = y : A) is an equivalence.
-- π_1 is univalent => Σ A P is a univalent subuniverse.

-- P : U -> U ; P _ = 1
-- Σ (X : U) 1 ≃ U is a univalent subuniverse.

-- Suppose P : U -> U, st, π_1 is univalent.
-- Claim: ∀ X, P(X) is a proposition.

-- lemma : ((x , b) (y , c) : Σ (x : A) B(x))
--       → ((x , b) == (y , c)) ≃ Σ (p : x == y) (b == c [B ↓ p])

-- P is univalent, so ∀ X Y,

-- myP X = trunc -1 X

-- myP ⊥ = ⊥

-- P : U -> U
-- P X = isEmpty(X) := (X = 0)

-- transport : (X : U , ϕ : isEmpty(X)) = (Y : U , ϕ : isEmpty(Y)) -> (X = Y)

-- ∀ P : U -> U,

-- El : X -> U, Ũ = Σ (X : U) El(X)

univ-transport : ∀ {i j} {P : Type i -> Type j} {X Y : Type i} {u : P X} {v : P Y} -> ((X , u) == ((Y , v))) -> (X == Y)
univ-transport = ap fst

univ-transport : ∀ {i j} {P : Type i -> Type j} {X Y : Type i} {u : P X} {v : P Y} -> (X == Y) -> ((X , u) == ((Y , v)))
univ-transport = ap fst


is-univ : ∀ {i j} {P : Type i -> Type j} {X Y : Type i} (u : P X) (v : P Y) -> is-equiv (univ-transport {P = P} {X} {Y} {u} {v})
is-univ = {!   !}

--    (X = Y : U)
-- ≃ ((X : U , u : P X) = (Y : U, v : P Y)) (by is-univ(P))
-- ≃ Σ (p : X = Y : U) (u == v [ P ↓ p ]) (by path space of Σ)

--   where u : P X
--         v : P Y

-- P is a univalent type family, iff transport : (x = y : A) -> P x ≃ P y is an equivalence.
-- P is univalent => π_1 is a univalent fibration.

-- P : U -> U is univalent if transport : (X = Y : U) -> (P X ≃ P Y) is an equivalence.
-- P = id is univalent.

-- P _ = 1, transport : (X = Y : U) -> (1 ≃ 1) is NOT an equivalence.
-- So, Σ (X : U) 1 ≃ U is NOT univalent?

-- P X = X, then Σ (X : U) X, pointed types.

-- Claim: For all P : U -> U, P is univalent if (iff?) ∀ x, P(x) is a proposition.

-- Claim: If ∀ x, P(x) is a proposition, then Σ U P is a univalent subuniverse of U.

-- Claim: UFin/UFin_n is a univalent subuniverse.