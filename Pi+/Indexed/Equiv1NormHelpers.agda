{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.Indexed.Equiv1NormHelpers where

open import lib.Base
open import lib.PathGroupoid
open import lib.types.Nat renaming (_+_ to _+ℕ_)
open import lib.types.Sigma
open import lib.types.Fin
open import lib.types.List
open import lib.NType

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.Indexed.Equiv0Norm
open import Pi+.Indexed.Equiv0Hat
open import Pi+.Indexed.Equiv1Hat
open import Pi+.Indexed.Equiv2Hat

open import Pi+.Misc
open import Pi+.Extra
open import Pi+.UFin.Base
open import Pi+.Common.FinHelpers
open import Pi+.Coxeter.Coxeter
open import Pi+.Coxeter.Sn

private
  variable
    n m o : ℕ

postulate
    ℕ-S-is-inj-rewrite : {n : ℕ} -> (ℕ-S-is-inj n n idp) ↦ idp -- path in ℕ
    {-# REWRITE ℕ-S-is-inj-rewrite #-}

ℕ-S-is-inj-idp : {n : ℕ} -> ℕ-S-is-inj (S n) (S n) idp == idp
ℕ-S-is-inj-idp = prop-has-all-paths {{has-level-apply ℕ-level _ _}} _ _

transpos2pi^ : {n : ℕ} → Fin n → (S n) ⟷₁^ (S n)
transpos2pi^ {S m} (O , lp) = swap₊^
transpos2pi^ {S m} (S fn , lp) = ⊕^ transpos2pi^ (fn , <-cancel-S lp)

list2pi^ : {m : ℕ} → List (Fin m) → (S m) ⟷₁^ (S m)
list2pi^ nil = id⟷₁^
list2pi^ (fn :: xs) = transpos2pi^ fn ◎^ list2pi^ xs

list2pi^++ : {m : ℕ} → (l r : List (Fin m)) →
              list2pi^ (l ++ r) ⟷₂^ list2pi^ l ◎^ list2pi^ r
list2pi^++ nil r = idl◎r^
list2pi^++ (n :: l) r = trans⟷₂^ (id⟷₂^ ⊡^ (list2pi^++ l r)) assoc◎l^

transpos-cancel^ : {n : ℕ} {k : Fin (S n)} →
                  transpos2pi^ k ◎^ transpos2pi^ k ⟷₂^ id⟷₁^
transpos-cancel^ {n} {k = k} = TODO -- eval^₂ (transpos-cancel {m = n} {n = k})

slide0-transpos^ : {m : ℕ}  {kp : 0 < S (S (S m))} →
                  (n : Fin (S (S (S m)))) → (1<n : 1 < fst n) →
  transpos2pi^ n ◎^ transpos2pi^ (0 , kp) ⟷₂^ transpos2pi^ (0 , kp) ◎^ transpos2pi^ n
slide0-transpos^ {m} {kp} n 1<n = TODO -- eval^₂ (slide0-transpos {m} {kp} n 1<n)

slide-transpos^ : {m : ℕ} → (n k : Fin (S m)) → (Sk<n : S (fst k) < fst n) →
  transpos2pi^ n ◎^ transpos2pi^ k ⟷₂^ transpos2pi^ k ◎^ transpos2pi^ n
slide-transpos^ {m} n k Sk<n = TODO -- eval^₂ (slide-transpos {m} n k Sk<n)

braid-transpos^ : {m : ℕ} → (n : Fin m) →
  transpos2pi^ S⟨ n ⟩ ◎^ transpos2pi^ ⟨ n ⟩ ◎^ transpos2pi^ S⟨ n ⟩ ⟷₂^
  transpos2pi^ ⟨ n ⟩ ◎^ transpos2pi^ S⟨ n ⟩ ◎^ transpos2pi^ ⟨ n ⟩
braid-transpos^ {m} n = TODO -- eval^₂ (braid-transpos {m} n)

cox≈2pi^ : {m : ℕ} {r₁ r₂ : List (Fin (S m))} → r₁ ≈₁ r₂ → list2pi^ r₁ ⟷₂^ list2pi^ r₂
cox≈2pi^ c = TODO -- eval^₂ (cox≈2pi c)

piRespectsCox^ : (n : ℕ) → (l₁ l₂ : List (Fin n)) → (l₁ ≈ l₂) →
                (list2pi^ l₁) ⟷₂^ (list2pi^ l₂)
piRespectsCox^ _ _ _ c = TODO -- eval^₂ (piRespectsCox _ _ _ c)

list2pi^I : (n == m) → List (Fin n) → S n ⟷₁^ S m
list2pi^I idp l = list2pi^ l

piRespectsCoxI : (p : n == m) → (l₁ l₂ : List (Fin n)) → (l₁ ≈ l₂) →
                (list2pi^I {n = n} {m = m} p l₁) ⟷₂^ (list2pi^I {n = n} {m = m} p l₂)
piRespectsCoxI idp _ _ c = piRespectsCox^ _ _ _ c

pi^2list : (S n) ⟷₁^ (S m) → List (Fin n)
pi^2list swap₊^ = fzero :: nil
pi^2list id⟷₁^ = nil
pi^2list (c ◎^ c₁) with (⟷₁^-eq-size c) | (⟷₁^-eq-size c₁)
... | idp | idp = pi^2list c ++ pi^2list c₁
pi^2list {O} (⊕^ c) = nil
pi^2list {S n} (⊕^ c) with (⟷₁^-eq-size c)
... | idp = map S⟨_⟩ (pi^2list c)

eval₁-map-S : {n : ℕ} → (l : List (Fin n)) → list2pi^ (map S⟨_⟩ l) ⟷₂^ ⊕^ (list2pi^ l)
eval₁-map-S nil = !⊕id⟷₁⟷₂^
eval₁-map-S ((x , xp) :: l) rewrite <-has-all-paths (<-cancel-S (<-ap-S xp)) xp =
  let rec = eval₁-map-S l
  in  trans⟷₂^ (id⟷₂^ ⊡^ rec) TODO -- hom◎⊕⟷₂^

pi^2list-◎^-β : {c₁ c₂ : S n ⟷₁^ S n} → pi^2list (c₁ ◎^ c₂) == pi^2list c₁ ++ pi^2list c₂
pi^2list-◎^-β = idp

pi^2list-!-β : {c : S n ⟷₁^ S n} → pi^2list (!⟷₁^ c) == reverse (pi^2list c)
pi^2list-!-β {O} {id⟷₁^} = idp
pi^2list-!-β {O} {c₁ ◎^ c₂} with (⟷₁^-eq-size c₁)
... | idp = ap (λ l → l ++ pi^2list (!⟷₁^ c₁)) (pi^2list-!-β {c = c₂})
          ∙ ap (λ l → reverse (pi^2list c₂) ++ l) (pi^2list-!-β {c = c₁})
          ∙ TODO
pi^2list-!-β {O} {⊕^ c} = TODO
pi^2list-!-β {S n} {c} = TODO

norm2norm : (c : S n ⟷₁^ S m) →
    (list2pi^I (ℕ-S-is-inj _ _ (⟷₁^-eq-size c)) (pi^2list c)) ⟷₂^ c
norm2norm (swap₊^ {n = n})
    rewrite (ℕ-p (+-assoc 1 1 n))
    rewrite (ℕ-p (+-unit-r 1))
    rewrite (ℕ-p (+-assoc 1 0 1)) =
    -- Code duplication with Eval1Hat
        _ ⟷₂^⟨ idr◎l^ ⟩
        _ ⟷₂^⟨ TODO {- idl◎l^ -} ⟩
        _ ⟷₂^⟨ idr◎l^ ⟩
        _ ⟷₂^⟨ ⊕⊕id⟷₁⟷₂^ ⊡^ ((id⟷₂^ ⊡^ ⊕⊕id⟷₁⟷₂^) ⊡^ (⊕⊕id⟷₁⟷₂^ ⊡^ ⊕⊕id⟷₁⟷₂^)) ⟩
        _ ⟷₂^⟨ idl◎l^ ⟩
        _ ⟷₂^⟨ idr◎l^ ⊡^ idl◎l^ ⟩
        _ ⟷₂^⟨ idr◎l^ ⟩
        swap₊^ ⟷₂^∎
norm2norm id⟷₁^ = id⟷₂^
norm2norm (c₁ ◎^ c₂) with (⟷₁^-eq-size c₂) | (⟷₁^-eq-size c₁)
... | idp | idp =
  let r₁ = norm2norm c₁
      r₂ = norm2norm c₂
      lemma = list2pi^++ (pi^2list c₁) (pi^2list c₂)
  in  trans⟷₂^ lemma (r₁ ⊡^ r₂)
norm2norm {O} (⊕^ c) with (⟷₁^-eq-size c)
... | idp = !⟷₂^ (trans⟷₂^ (resp⊕⟷₂ (c₊⟷₂id⟷₁ c)) ⊕id⟷₁⟷₂^)
norm2norm {S n} (⊕^ c) with (⟷₁^-eq-size c)
... | idp =
  let rec = norm2norm c
      l = eval₁-map-S ((pi^2list c))
  in  trans⟷₂^ l (resp⊕⟷₂ rec)

pi^2list-id : {n : ℕ} → pi^2list (⊕^ (id⟷₁^ {n = n})) == nil
pi^2list-id {O} = idp
pi^2list-id {S n} = idp

eval^₁-transpos : (k : Fin n) → (pi^2list (transpos2pi^ k)) == k :: nil
eval^₁-transpos {S n} (O , pk)
    rewrite (ℕ-p (+-assoc 1 1 n))
    rewrite (ℕ-p (+-unit-r 1))
    rewrite (ℕ-p (+-assoc 1 0 1))
    rewrite pi^2list-id {n} = TODO -- List=-out ((Fin= _ _ idp _ _) , idp)
eval^₁-transpos {S n} (S k , pk) =
  let rec = ap (map S⟨_⟩) (eval^₁-transpos {n} (k , <-cancel-S pk))
  in  TODO -- rec ∙ List=-out ((Fin= _ _ idp _ _) , idp)

list2list : {n : ℕ} → (p : List (Fin n)) → pi^2list (list2pi^I idp p) == p
list2list nil = idp
list2list {S n} ((k , pk) :: xs)
  rewrite (eval^₁-transpos (k , pk)) =
    let rec = list2list xs
    in  List=-out ((pair= idp (<-has-all-paths _ _)) , rec)
