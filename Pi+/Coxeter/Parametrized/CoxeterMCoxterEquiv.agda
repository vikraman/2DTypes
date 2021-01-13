{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Parametrized.CoxeterMCoxterEquiv where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.Equivalence
open import lib.types.List 

open import Pi+.Misc
open import Pi+.Extra
open import Pi+.Coxeter.Common.Arithmetic
open import Pi+.Coxeter.Common.ListN
open import Pi+.Coxeter.Common.LList
open import Pi+.Coxeter.NonParametrized.MCoxeter
open import Pi+.Coxeter.Parametrized.ListFinLListEquiv
open import Pi+.Coxeter.Parametrized.Group

  
-- long-swap-lemma : (n k x : ℕ) -> (k + n < x) -> ((n ↓ k) ++ x ∷ nil) ~ (x ∷ (n ↓ k))
-- long-swap-lemma n 0 x p = idp~
-- long-swap-lemma n (S k) x p = trans~ (respects-l~ [ k + n ] (long-swap-lemma n k x (≤-down p)) idp idp) (respects-r~ (n ↓ k) (comm~ (swap~ p)) idp idp)

-- long-lemma : (n k : ℕ) -> ((n ↓ (2 + k)) ++ S (k + n) ∷ nil) ~ (k + n ∷ (n ↓ (2 + k)))
-- long-lemma n 0 = braid~
-- long-lemma n (S k) = trans~ (respects-l~ (_ ∷ _ ∷ nil) (long-swap-lemma n (1 + k) (2 + k + n) rrr) idp idp) (respects-r~ _ braid~ idp idp)

-- mcoxeter≅->coxeter : (m1 m2 : List) -> (m1 ≅ m2) -> (m1 ~ m2)
-- mcoxeter≅->coxeter m1 m2 (cancel≅ l r .m1 .m2 defm defmf) = respects-l~ l (respects-r~ r cancel~ idp idp) defm defmf
-- mcoxeter≅->coxeter m1 m2 (swap≅ x l r .m1 .m2 defm defmf) = respects-l~ l (respects-r~ r (swap~ x) idp idp) defm defmf
-- mcoxeter≅->coxeter m1 m2 (long≅ {n} k nil r .m1 .m2 defm defmf) = respects-r~ r (long-lemma n k) (≡-trans defm (≡-sym (++-assoc (n ↓ (2 + k)) [ 1 + k + n ] r))) defmf
-- mcoxeter≅->coxeter (x₁ ∷ m1) (x₂ ∷ m2) (long≅ k (x ∷ l) r .(x₁ ∷ m1) .(x₂ ∷ m2) defm defmf) =
--   let rec = mcoxeter≅->coxeter m1 m2 (long≅ k l r m1 m2 (cut-head defm) (cut-head defmf))
--   in  respects-l~ [ x ] rec (head+tail (cut-tail defm) idp) (head+tail (cut-tail defmf) idp)

-- mcoxeter≅*->coxeter : (m1 m2 : List) -> (m1 ≅* m2) -> (m1 ~ m2)
-- mcoxeter≅*->coxeter m1 .m1 idp = idp~
-- mcoxeter≅*->coxeter m1 m2 (trans≅ x p) = trans~ ((mcoxeter≅->coxeter _ _ x)) ((mcoxeter≅*->coxeter _ _ p))

mcoxeter->coxeter : {n : ℕ} -> (m1 m2 : LList n) -> ((m1 .fst) ↔ (m2 .fst)) -> (<– List≃LList m1) ≈[ n ] (<– List≃LList m2)
mcoxeter->coxeter = {!   !}

-- coxeter->mcoxeters : {m1 m2 : List} -> (m1 ~ m2) -> (m1 ≃s* m2)
-- coxeter->mcoxeters (cancel~ {n}) = trans≃s (cancel≃s nil nil (n ∷ n ∷ nil) nil idp idp) idp≃s
-- coxeter->mcoxeters (swap~ {n} {k} x) = trans≃s (swap≃s x nil nil (n ∷ k ∷ nil) (k ∷ n ∷ nil) idp idp) idp≃s
-- coxeter->mcoxeters (braid~ {n}) = trans≃s (long≃s O nil nil (S n ∷ n ∷ S n ∷ nil) (n ∷ S n ∷ n ∷ nil) idp idp) idp≃s
-- coxeter->mcoxeters (respects-l~ l p pm1 pm2) = 
--     let lemma = l++≃s* l (coxeter->mcoxeters p)
--     in  transport2 (λ a b → a ≃s* b) (! pm1) (! pm2) lemma
-- coxeter->mcoxeters (respects-r~ r p pm1 pm2) = 
--     let lemma = ++r≃s* r (coxeter->mcoxeters p)
--     in  transport2 (λ a b → a ≃s* b) (! pm1) (! pm2) lemma
-- coxeter->mcoxeters (idp~ {m}) = idp≃s
-- coxeter->mcoxeters (comm~ {m1} {m2} p) = trans≃s* (comm≃s* {_} {_} {m2} (coxeter->mcoxeters p)) idp≃s
-- coxeter->mcoxeters (trans~ p p₁) = trans≃s* (coxeter->mcoxeters p) (coxeter->mcoxeters p₁)

-- coxeter->mcoxeter : {m1 m2 : List} -> (m1 ~ m2) -> (m1 ≃ m2)
-- coxeter->mcoxeter = mcoxeters*->mcoxeter ∘ coxeter->mcoxeters 

coxeter->mcoxeter :  {n : ℕ} -> {m1 m2 : List (Fin n)} -> (m1 ≈[ n ] m2) -> (–> List≃LList m1) .fst ↔ (–> List≃LList m2) .fst
coxeter->mcoxeter = {!   !}
