{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module PiFin+.Semantics4 where

open import HoTT
open import PiFin+.Semantics0
open import PiFin+.Semantics1
open import PiFin+.Semantics2

data Perm : ℕ → Type₀ where
  [] : Perm 0
  ins : {n i : ℕ}
      → (w : i < S n) → (p : Perm n) → Perm (S n)

ins= : {n : ℕ} → {i i' : ℕ} → i == i'
     → {a : i < S n} → {a' : i' < S n}
     → {p p' : Perm n} → p == p'
     → ins a p == ins a' p'
ins= idp idp = ap (λ a → ins a _) (prop-has-all-paths _ _)

infixr 80 _∷_
data Vec {ℓ} (X : Type ℓ) : ℕ → Type ℓ where
  [] : Vec X 0
  _∷_ : {n : ℕ} → (x : X) → Vec X n → Vec X (S n)

record Vec* {ℓ} (X : Type ℓ) (n : ℕ) : Type ℓ where
  constructor mkVec*
  field
    v : Vec X n
    i : Σ ℕ (λ i → i < n)

record Vec** {ℓ} (X : Type ℓ) (n : ℕ) : Type ℓ where
  constructor mkVec**
  field
    v : Vec X n
    i : Σ ℕ (λ i → i < S n)
    x₀ : X

insert : ∀ {ℓ} {X : Type ℓ} {n : ℕ} → Vec** X n → Vec* X (S n)
insert (mkVec** v (O , a) x₀) = mkVec* (x₀ ∷ v) (O , a)
insert (mkVec** [] (S i , ltSR ()) x₀)
insert (mkVec** (x ∷ v) (S i , ltS) x₀) =
  let r = insert (mkVec** v (i , ltS) x₀) in
    mkVec* (x ∷ Vec*.v r) (S i , ltS)
insert (mkVec** (x ∷ v) (S i , ltSR a) x₀) =
  let r = insert (mkVec** v (S i , a) x₀) in
    mkVec* (x ∷ Vec*.v r) (S i , ltSR a)

display-perm : {n : ℕ} → Perm n → Vec ℕ n
display-perm [] = []
display-perm {S n} (ins a p) =
  Vec*.v (insert (mkVec** (display-perm p) (_ , a) n))

module PermExamples where

  ex1 : Perm 0
  ex1 = []

  ex2 : Perm 1
  ex2 = ins ltS []

  ex3 : Perm 2
  ex3 = ins ltS (ins ltS [])

  ex4 : Perm 2
  ex4 = ins (ltSR ltS) (ins ltS [])

  ex5 : Perm 3
  ex5 = ins (ltSR (ltSR ltS)) (ins (ltSR ltS) (ins ltS []))

  ex3' : display-perm ex3 == 0 ∷ 1 ∷ []
  ex3' = idp

  ex4' : display-perm ex4 == 1 ∷ 0 ∷ []
  ex4' = idp

  ex5' : display-perm ex5 == 2 ∷ 1 ∷ 0 ∷ []
  ex5' = idp

record Perm* (n : ℕ) : Type₀ where
  constructor mkPerm*
  field
    p : Perm n
    i : Σ ℕ (λ i → i < S n)

mkPerm*= : {n : ℕ} → {p p' : Perm n} → p == p'
         → {i i' : ℕ} → i == i'
         → {a : i < S n} → {a' : i' < S n}
         → mkPerm* p (i , a) == mkPerm* p' (i' , a')
mkPerm*= {p = p} idp {i} idp =
  ap (λ a → mkPerm* p (i , a)) (prop-has-all-paths _ _)

{- This equivalence is useful for proving some ℕ-indexed type is
   equivalent to Perm by induction. -}

perm-pred : {n : ℕ} → Perm (S n) → Perm* n
perm-pred (ins w p) = mkPerm* p (_ , w)

perm-succ : {n : ℕ} → Perm* n → Perm (S n)
perm-succ (mkPerm* p (_ , a)) = ins a p

perm-succ-η-p : {n : ℕ} → (p : Perm* n)
              → Perm*.p (perm-pred (perm-succ p)) == Perm*.p p
perm-succ-η-p (mkPerm* p i) = idp

perm-succ-η-i : {n : ℕ} → (p : Perm* n)
              → Perm*.i (perm-pred (perm-succ p)) == Perm*.i p
perm-succ-η-i (mkPerm* p i) = pair= idp idp

perm-succ-η : {n : ℕ} → perm-pred ∘ perm-succ {n} ∼ idf (Perm* n)
perm-succ-η p = mkPerm*= (perm-succ-η-p p) (ap fst (perm-succ-η-i p))

perm-succ-ε : {n : ℕ} → perm-succ ∘ perm-pred {n} ∼ idf (Perm (S n))
perm-succ-ε (ins w p) = ins= idp idp

Perm*≃Perm : {n : ℕ} → Perm* n ≃ Perm (S n)
Perm*≃Perm = equiv perm-succ perm-pred perm-succ-ε perm-succ-η

El=→Perm : {n : ℕ} → El n == El n → Perm n
El=→Perm {O} p = []
El=→Perm {S n} p = ins ltS (El=→Perm (⊤-cncl p))

El=→Perm* : {n : ℕ} → El n == El n → Perm* (S n)
El=→Perm* {O} p =
  mkPerm* (ins ltS []) (1 , ltS)
El=→Perm* {S n} p =
  let r = El=→Perm (⊤-cncl p) in
    mkPerm* (ins ltS (ins ltS r)) (S (S n) , ltS)

Perm→El= : {n : ℕ} → Perm n → El n == El n
Perm→El= {O} [] = idp
Perm→El= {S n} (ins ltS p) = ap (_⊔_ ⊤) (Perm→El= p)
Perm→El= {S n} (ins (ltSR w) p) = `swap₊ 1 n ∙ ap El (+-comm n 1)

Perm*→El= : {n : ℕ} → Perm* n → El (S n) == El (S n)
Perm*→El= p = Perm→El= (perm-succ p)

El=≃Perm-η : {n : ℕ} → (p : El n == El n) → Perm→El= (El=→Perm p) == p
El=≃Perm-η {O} p = prop-has-all-paths idp p
El=≃Perm-η {S n} p = {!!}

El=≃Perm-ε : {n : ℕ} → (p : Perm n) → El=→Perm (Perm→El= p) == p
El=≃Perm-ε {O} [] = idp
El=≃Perm-ε {S n} (ins ltS p) = ins= idp (El=≃Perm-ε p)
El=≃Perm-ε {S n} (ins (ltSR w) p) = ins= {!!} (El=≃Perm-ε p)

-- El=≃Perm : {n : ℕ} → (El n == El n) ≃ Perm n
-- El=≃Perm = equiv El=→Perm Perm→El= {!!} {!!}

-- El=≃Perm {O} =
--   equiv (λ _ → []) (λ _ → idp) (λ { [] → idp }) (λ { a → prop-has-all-paths idp a })
-- El=≃Perm {S n} =
--   let e = El=≃Perm {n} in
--     equiv {!!} {!!} {!!} {!!}
