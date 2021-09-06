{-# OPTIONS --without-K --rewriting #-}

module Pi.Coxeter.NonParametrized.MCoxeterS where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.PathGroupoid

open import Pi.Misc
open import Pi.Common.Arithmetic
open import Pi.Common.ListN
open import Pi.Coxeter.NonParametrized.MCoxeter
open import Pi.Coxeter.NonParametrized.ReductionRel
open import Pi.Coxeter.NonParametrized.Diamond

data _↔s_ : Listℕ -> Listℕ -> Type₀ where
    cancel↔s : {n : ℕ} -> (l r m mf : Listℕ) -> (defm : m == l ++ n ∷ n ∷ r) -> (defmf : mf == l ++ r) -> (m ↔s mf)
    swap↔s : {n : ℕ} -> {k : ℕ} -> (S k < n) ->  (l r m mf : Listℕ) -> (defm : m == l ++ n ∷ k ∷ r) -> (defmf : mf == l ++ k ∷ n ∷ r) -> (m ↔s mf)
    long↔s : {n : ℕ} -> (k : ℕ) -> (l r m mf : Listℕ) -> (defm : m == l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) -> (defmf : mf == l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r) -> (m ↔s mf)
    comm↔s : {m1 m2 : Listℕ} -> (m1 ↔s m2) -> (m2 ↔s m1)

data _↔s*_ : Listℕ -> Listℕ -> Type₀ where
    idp↔s : {m : Listℕ} -> m ↔s* m
    trans↔s : {m1 m2 m3 : Listℕ} -> (m1 ↔s m2) -> (m2 ↔s* m3) -> m1 ↔s* m3


trans↔s* : {m1 m2 m3 : Listℕ} -> (m1 ↔s* m2) -> (m2 ↔s* m3) -> m1 ↔s* m3
trans↔s* idp↔s p = p
trans↔s* (trans↔s x q) p = trans↔s x (trans↔s* q p)

comm↔s* : {m1 m2 m3 : Listℕ} -> (m1 ↔s* m2) -> m2 ↔s* m1
comm↔s* idp↔s = idp↔s
comm↔s* {m1} {m2} {m3} (trans↔s x q) = 
    let x' = comm↔s x
        q' = comm↔s* {_} {_} {m2} q
    in  trans↔s* q' (trans↔s (comm↔s x) idp↔s)

l++↔s : (m1 m2 l : Listℕ) -> (m1 ↔s m2) -> ((l ++ m1) ↔s (l ++ m2))
l++↔s m1 m2 l (cancel↔s l₁ r .m1 .m2 defm defmf) =  cancel↔s (l ++ l₁) r _ _ (≡-trans (start+end idp defm) (≡-sym (++-assoc l l₁ _))) ((≡-trans (start+end idp defmf) (≡-sym (++-assoc l l₁ _))))
l++↔s m1 m2 l (swap↔s x l₁ r .m1 .m2 defm defmf) =  swap↔s x (l ++ l₁) r _ _ (≡-trans (start+end idp defm) (≡-sym (++-assoc l l₁ _))) ((≡-trans (start+end idp defmf) (≡-sym (++-assoc l l₁ _))))
l++↔s m1 m2 l (long↔s k l₁ r .m1 .m2 defm defmf) =  long↔s k (l ++ l₁) r _ _ (≡-trans (start+end idp defm) (≡-sym (++-assoc l l₁ _))) ((≡-trans (start+end idp defmf) (≡-sym (++-assoc l l₁ _))))
l++↔s m1 m2 l (comm↔s p) = comm↔s (l++↔s m2 m1 l p)

l++↔s* : (l : Listℕ) -> {m1 m2 : Listℕ} -> (m1 ↔s* m2) -> ((l ++ m1) ↔s* (l ++ m2))
l++↔s* l idp↔s = idp↔s
l++↔s* l (trans↔s x p) = trans↔s (l++↔s _ _ l x) ((l++↔s* l p))

++r↔s : (m1 m2 r : Listℕ) -> (m1 ↔s m2) -> ((m1 ++ r) ↔s (m2 ++ r))
++r↔s m1 m2 r (cancel↔s l r₁ .m1 .m2 defm defmf) = cancel↔s l (r₁ ++ r)  _ _  (≡-trans (start+end defm idp) (++-assoc l _ r)) ((≡-trans (start+end defmf idp) (++-assoc l _ r)))
++r↔s m1 m2 r (swap↔s x l r₁ .m1 .m2 defm defmf) = swap↔s x l (r₁ ++ r)  _ _  (≡-trans (start+end defm idp) (++-assoc l _ r)) ((≡-trans (start+end defmf idp) (++-assoc l _ r)))
++r↔s m1 m2 r (long↔s k l r₁ .m1 .m2 defm defmf) = long↔s k l (r₁ ++ r)  _ _
  (≡-trans (start+end defm idp) (≡-trans (++-assoc l _ r) (start+end (idp {a = l}) (head+tail idp (head+tail idp (++-assoc (_ ↓ k) _ r))))))
  ((≡-trans (start+end defmf idp) (≡-trans (++-assoc l _ r) (start+end (idp {a = l}) (head+tail idp (head+tail idp (head+tail idp (++-assoc _ r₁ r))))))))
++r↔s m1 m2 l (comm↔s p) = comm↔s (++r↔s m2 m1 l p)

++r↔s* : {m1 m2 : Listℕ} -> (r : Listℕ) -> (m1 ↔s* m2) -> ((m1 ++ r) ↔s* (m2 ++ r))
++r↔s* r idp↔s = idp↔s
++r↔s* r (trans↔s x p) = trans↔s (++r↔s _ _ r x) (++r↔s* r p)

mcoxeters->mcoxeter : {m1 m2 : Listℕ} -> (m1 ↔s m2) -> (m1 ↔ m2)
mcoxeters->mcoxeter {m1} {m2} (cancel↔s l r .m1 .m2 defm defmf) = MC {_} {_} {m2} (trans≅ (cancel≅ l r m1 m2 defm defmf) idp) idp
mcoxeters->mcoxeter {m1} {m2} (swap↔s x l r .m1 .m2 defm defmf) = MC {_} {_} {m2} (trans≅ (swap≅ x l r m1 m2 defm defmf) idp) idp
mcoxeters->mcoxeter {m1} {m2} (long↔s k l r .m1 .m2 defm defmf) = MC {_} {_} {m2} (trans≅ (long≅ k l r m1 m2 defm defmf) idp) idp
mcoxeters->mcoxeter {m1} {m2} (comm↔s {.m2} {.m1} p) with mcoxeters->mcoxeter p
... | MC {_} {_} {mf} p1 p2 = MC {_} {_} {mf} p2 p1 

mcoxeters*->mcoxeter : {m1 m2 : Listℕ} -> (m1 ↔s* m2) -> (m1 ↔ m2)
mcoxeters*->mcoxeter {m1} {.m1} idp↔s = MC idp idp
mcoxeters*->mcoxeter {m1} {m2} (trans↔s x p) with mcoxeters*->mcoxeter p
... | MC {m3} {m2} {mf} p1 p2 with mcoxeters->mcoxeter x
...     | MC {m1} {m3} {mf'} p3 p4 with diamond-full p1 p4
...         | m , (pmf , pmf') = MC {_} {_} {m} (trans p3 pmf') (trans p2 pmf)


mcoxeter≅->mcoxeters* : {m1 m2 : Listℕ} -> (m1 ≅ m2) -> (m1 ↔s m2)
mcoxeter≅->mcoxeters* {m1} {m2} (cancel≅ l r .m1 .m2 defm defmf) = cancel↔s l r m1 m2 defm defmf
mcoxeter≅->mcoxeters* {m1} {m2} (swap≅ x l r .m1 .m2 defm defmf) = swap↔s x l r m1 m2 defm defmf
mcoxeter≅->mcoxeters* {m1} {m2} (long≅ k l r .m1 .m2 defm defmf) = long↔s k l r m1 m2 defm defmf

mcoxeter≅*->mcoxeters* : {m1 m2 : Listℕ} -> (m1 ≅* m2) -> (m1 ↔s* m2)
mcoxeter≅*->mcoxeters* {m1} {.m1} idp = idp↔s
mcoxeter≅*->mcoxeters* {m1} {m2} (trans≅ x p) = trans↔s (mcoxeter≅->mcoxeters* x) (mcoxeter≅*->mcoxeters* p)

mcoxeter->mcoxeters* : {m1 m2 : Listℕ} -> (m1 ↔ m2) -> (m1 ↔s* m2)
mcoxeter->mcoxeters* {m1} {m2} (MC {_} {_} {mf} p1 p2) = 
    let q1 = mcoxeter≅*->mcoxeters* p1
        q2 = mcoxeter≅*->mcoxeters* p2
    in  trans↔s* q1 (comm↔s* {_} {_} {mf} q2)