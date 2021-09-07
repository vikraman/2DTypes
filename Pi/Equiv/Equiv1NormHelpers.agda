{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.Equiv.Equiv1NormHelpers where

open import lib.Base
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.types.Nat renaming (_+_ to _+ℕ_)
open import lib.types.Sigma
open import lib.types.Fin
open import lib.types.List
open import lib.NType

open import Pi.Syntax.Pi+.Indexed as Pi
open import Pi.Syntax.Pi^ as Pi^
open import Pi.Syntax.Pi^Helpers as Pi^
open import Pi.Equiv.Equiv0Norm
open import Pi.Equiv.Equiv0Hat
open import Pi.Equiv.Equiv1Hat

open import Pi.Common.Misc
open import Pi.Common.Extra
open import Pi.UFin.Base
open import Pi.Common.FinHelpers
open import Pi.Coxeter.Coxeter
open import Pi.Coxeter.Sn

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
list2pi^++ (n :: l) r = _■^_ (id⟷₂^ ⊡^ (list2pi^++ l r)) assoc◎l^

transpos-cancel^ : {n : ℕ} {k : Fin n} →
                  transpos2pi^ k ◎^ transpos2pi^ k ⟷₂^ id⟷₁^
transpos-cancel^ {S n} {k = O , p0} = linv◎l^
transpos-cancel^ {S n} {k = S k , pk} = hom◎⊕⟷₂^ ■^ (resp⊕⟷₂ transpos-cancel^ ■^ ⊕id⟷₁⟷₂^)

postulate
  n≰n : {n : ℕ} → ¬ (n < n)

slide-transpos^ : {m : ℕ} → (k n : Fin (S m)) → (Sk<n : S (fst k) < fst n) →
  transpos2pi^ n ◎^ transpos2pi^ k ⟷₂^ transpos2pi^ k ◎^ transpos2pi^ n
slide-transpos^ {O} (.0 , ltS) (.0 , ltS) Sk<n = id⟷₂^
slide-transpos^ {O} (k , ltSR ()) (.0 , ltS) Sk<n
slide-transpos^ {O} (k , pk) (n , ltSR ()) Sk<n
slide-transpos^ {S m} (O , pk) (S O , pn) (ltSR ())
slide-transpos^ {S m} (O , pk) (S (S n) , pn) Sk<n = swapr₊⟷₂^
slide-transpos^ {S m} (S k , pk) (S n , pn) Sk<n =
  let rec = slide-transpos^ ((k , <-cancel-S pk)) (n , <-cancel-S pn) (<-cancel-S Sk<n)
  in  hom◎⊕⟷₂^ ■^ (resp⊕⟷₂ rec ■^ hom⊕◎⟷₂^)

braid-transpos^ : {m : ℕ} → (n : Fin m) →
  transpos2pi^ S⟨ n ⟩ ◎^ transpos2pi^ ⟨ n ⟩ ◎^ transpos2pi^ S⟨ n ⟩ ⟷₂^
  transpos2pi^ ⟨ n ⟩ ◎^ transpos2pi^ S⟨ n ⟩ ◎^ transpos2pi^ ⟨ n ⟩
braid-transpos^ {S m} (O , p0) = hexagonl₊r
braid-transpos^ {S m} (S n , pn)
  rewrite <-has-all-paths (<-cancel-S (<-ap-S pn)) (<-ap-S (<-cancel-S pn))
  rewrite <-has-all-paths (<-trans ltS pn) (ltSR (<-cancel-S pn)) =
  let rec = braid-transpos^ (n , <-cancel-S pn)
  in
    _ ⟷₂^⟨ id⟷₂^ ⊡^ hom◎⊕⟷₂^ ⟩
    _ ⟷₂^⟨ hom◎⊕⟷₂^ ⟩
    _ ⟷₂^⟨ resp⊕⟷₂ rec ⟩
    _ ⟷₂^⟨ !⟷₂^ hom◎⊕⟷₂^ ⟩
    _ ⟷₂^⟨ !⟷₂^ (id⟷₂^ ⊡^ hom◎⊕⟷₂^) ⟩
    _ ⟷₂^∎

cox≈2pi^ : {m : ℕ} {r₁ r₂ : List (Fin (S m))} → r₁ ≈* r₂ → list2pi^ r₁ ⟷₂^ list2pi^ r₂
cox≈2pi^ (≈-rel cancel) = (id⟷₂^ ⊡^ idr◎l^) ■^ transpos-cancel^
cox≈2pi^ (≈-rel (swap x)) = (id⟷₂^ ⊡^ idr◎l^) ■^ (slide-transpos^ _ _ x ■^ !⟷₂^ (id⟷₂^ ⊡^ idr◎l^))
cox≈2pi^ (≈-rel braid) = (id⟷₂^ ⊡^ (id⟷₂^ ⊡^ idr◎l^))  ■^ (braid-transpos^ _ ■^ !⟷₂^ ((id⟷₂^ ⊡^ (id⟷₂^ ⊡^ idr◎l^))))
cox≈2pi^ idp = id⟷₂^
cox≈2pi^ (comm c) = !⟷₂^ (cox≈2pi^ c)
cox≈2pi^ (trans c c₁) = cox≈2pi^ c ■^ cox≈2pi^ c₁
cox≈2pi^ (respects-++ c c₁) = list2pi^++ _ _ ■^ ((cox≈2pi^ c ⊡^ cox≈2pi^ c₁) ■^ !⟷₂^ (list2pi^++ _ _))

piRespectsCox^ : (n : ℕ) → (l₁ l₂ : List (Fin n)) → (l₁ ≈* l₂) →
                (list2pi^ l₁) ⟷₂^ (list2pi^ l₂)
piRespectsCox^ O nil nil c = id⟷₂^
piRespectsCox^ (S n) _ _ c = cox≈2pi^ c

list2pi^I : (n == m) → List (Fin n) → S n ⟷₁^ S m
list2pi^I idp l = list2pi^ l

piRespectsCoxI : (p : n == m) → (l₁ l₂ : List (Fin n)) → (l₁ ≈* l₂) →
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
  in  _■^_ (id⟷₂^ ⊡^ rec) hom◎⊕⟷₂^

pi^2list-◎^-β : {c₁ c₂ : S n ⟷₁^ S n} → pi^2list (c₁ ◎^ c₂) == pi^2list c₁ ++ pi^2list c₂
pi^2list-◎^-β = idp

module _ where

  pi^2list-!^-β : (c : (S n) ⟷₁^ (S m)) → pi^2list (!⟷₁^ c) == transport (λ k → List (Fin k)) (ℕ-S-is-inj _ _ (⟷₁^-eq-size c)) (reverse (pi^2list c))
  pi^2list-!^-β swap₊^ = idp
  pi^2list-!^-β id⟷₁^ = idp
  pi^2list-!^-β (c₁ ◎^ c₂) with (⟷₁^-eq-size c₁) with (⟷₁^-eq-size c₂)
  ... | idp | idp =
    let r₁ = pi^2list-!^-β c₁
        r₂ = pi^2list-!^-β c₂
    in  ap2 (λ l₁ l₂ → l₁ ++ l₂) r₂ r₁ ∙ ! (reverse-++ (pi^2list c₁) (pi^2list c₂))
  pi^2list-!^-β {O} (⊕^ c) with (⟷₁^-eq-size c)
  ... | idp = idp
  pi^2list-!^-β {S n} (⊕^ c) with (⟷₁^-eq-size c)
  ... | idp = ap (map S⟨_⟩) (pi^2list-!^-β c) ∙ ! (reverse-map S⟨_⟩ (pi^2list c))


pi^2list2pi^ : (c : S n ⟷₁^ S m) →
    (list2pi^I (ℕ-S-is-inj _ _ (⟷₁^-eq-size c)) (pi^2list c)) ⟷₂^ c
pi^2list2pi^ (swap₊^ {n = n})
    rewrite (ℕ-p (+-assoc 1 1 n))
    rewrite (ℕ-p (+-unit-r 1))
    rewrite (ℕ-p (+-assoc 1 0 1)) = idr◎l^
pi^2list2pi^ id⟷₁^ = id⟷₂^
pi^2list2pi^ (c₁ ◎^ c₂) with (⟷₁^-eq-size c₂) | (⟷₁^-eq-size c₁)
... | idp | idp =
  let r₁ = pi^2list2pi^ c₁
      r₂ = pi^2list2pi^ c₂
      lemma = list2pi^++ (pi^2list c₁) (pi^2list c₂)
  in  _■^_ lemma (r₁ ⊡^ r₂)
pi^2list2pi^ {O} (⊕^ c) with (⟷₁^-eq-size c)
... | idp = !⟷₂^ (_■^_ (resp⊕⟷₂ (c₊⟷₂id⟷₁^ c)) ⊕id⟷₁⟷₂^)
pi^2list2pi^ {S n} (⊕^ c) with (⟷₁^-eq-size c)
... | idp =
  let rec = pi^2list2pi^ c
      l = eval₁-map-S ((pi^2list c))
  in  _■^_ l (resp⊕⟷₂ rec)

pi^2list-id : {n : ℕ} → pi^2list (⊕^ (id⟷₁^ {n = n})) == nil
pi^2list-id {O} = idp
pi^2list-id {S n} = idp

eval^₁-transpos : (k : Fin n) → (pi^2list (transpos2pi^ k)) == k :: nil
eval^₁-transpos {S n} (O , pk)
    rewrite (ℕ-p (+-assoc 1 1 n))
    rewrite (ℕ-p (+-unit-r 1))
    rewrite (ℕ-p (+-assoc 1 0 1))
    rewrite pi^2list-id {n} = List=-out ((Fin= _ _ idp _ _) , idp)
eval^₁-transpos {S n} (S k , pk) =
  let rec = ap (map S⟨_⟩) (eval^₁-transpos {n} (k , <-cancel-S pk))
  in  rec ∙ List=-out ((Fin= _ _ idp _ _) , idp)

list2list : {n : ℕ} → (p : List (Fin n)) → pi^2list (list2pi^I idp p) == p
list2list nil = idp
list2list {S n} ((k , pk) :: xs)
  rewrite (eval^₁-transpos (k , pk)) =
    let rec = list2list xs
    in  List=-out ((pair= idp (<-has-all-paths _ _)) , rec)
