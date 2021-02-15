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

open import Pi+.Misc
open import Pi+.Extra
open import Pi+.UFin.Base
open import Pi+.Common.FinHelpers
open import Pi+.Coxeter.Coxeter
open import Pi+.Coxeter.Sn

private
  variable
    n m o : ℕ

transpos2pi : {t : U^ (S n)} → (Fin n) → t ⟷₁^ t
transpos2pi {S n} {I+ I+ t} (O , lp) = swap₊^
transpos2pi {S n} {I+ I+ t} (S x , lp) = ⊕^ transpos2pi (x , (<-cancel-S lp)) 

transpos-cancel : {m : ℕ} {t : U^ (S (S m))} → {n : Fin (S m)} →
                  transpos2pi {t = t} n ◎^ transpos2pi {t = t} n ⟷₂^ id⟷₁^
transpos-cancel {m} {n} = TODO

-- slide0-transpos : {m : ℕ}  {kp : 0 < S (S (S m))} →
--                   (n : Fin (S (S (S m)))) → (1<n : 1 < fst n) →
--   transpos2pi n ◎^ transpos2pi (0 , kp) ⟷₂^ transpos2pi (0 , kp) ◎^ transpos2pi n
-- slide0-transpos = TODO

-- slide-transpos : {m : ℕ} → (n k : Fin (S m)) → (Sk<n : S (fst k) < fst n) →
--   transpos2pi n ◎^ transpos2pi k ⟷₂^ transpos2pi k ◎^ transpos2pi n
-- slide-transpos {O} (.(S (S k)) , ltSR ()) (k , kp) ltS
-- slide-transpos {O} (.(S _) , ltSR ()) (k , kp) (ltSR lp)
-- slide-transpos {S O} (.(S (S k)) , ltSR (ltSR ())) (k , kp) ltS
-- slide-transpos {S O} (.(S _) , ltSR (ltSR ())) (k , p) (ltSR lp)
-- slide-transpos {S (S m)} n (O , kp) lp = slide0-transpos {kp = kp} n lp
-- slide-transpos {S (S m)} (S O , np) (S k , kp) (ltSR ())
-- slide-transpos {S (S m)} (S (S O) , np) (S k , kp) (ltSR (ltSR ()))
-- slide-transpos {S (S m)} (S (S (S n)) , np) (S k , kp) lp =
--   let rn0 = transpos2pi (S (S n) , <-cancel-S np)
--       rk0 = transpos2pi (k , <-cancel-S kp)
--   in transpos2pi (S (S (S n)) , np) ◎^ transpos2pi (S k , kp)
--        ⟷₂^⟨ id⟷₂^ ⟩
--      (⊕^ rn0) ◎^ (⊕^ rk0)
--        ⟷₂^⟨ hom◎⊕⟷₂^ ⟩
--      ⊕^ (rn0 ◎^ rk0)
--        ⟷₂^⟨ resp⊕⟷₂ 
--          (slide-transpos (S (S n) , <-cancel-S np) (k , <-cancel-S kp) (<-cancel-S lp))  ⟩
--      ⊕^ (rk0 ◎^ rn0)
--        ⟷₂^⟨ hom⊕◎⟷₂^ ⟩
--      (⊕^ rk0) ◎^ (⊕^ rn0)
--        ⟷₂^⟨ id⟷₂^ ⟩
--      transpos2pi (S k , kp) ◎^ transpos2pi (S (S (S n)) , np)
--        ⟷₂^∎


-- braid-transpos : {m : ℕ} → (n : Fin m) →
--   transpos2pi S⟨ n ⟩ ◎^ transpos2pi ⟨ n ⟩ ◎^ transpos2pi S⟨ n ⟩ ⟷₂^
--   transpos2pi ⟨ n ⟩ ◎^ transpos2pi S⟨ n ⟩ ◎^ transpos2pi ⟨ n ⟩
-- braid-transpos {m} n = TODO

-- -- Mapping the entire list of transpositions to a combinator and
-- -- some properties

list2norm : {t : U^ (S n)} → List (Fin n) → t ⟷₁^ t
list2norm nil = id⟷₁^
list2norm ((fs , fp) :: xs) = (transpos2pi (fs , fp)) ◎^ (list2norm xs) -- 

list2normI : {t₁ : U^ (S n)} {t₂ : U^ (S m)} → (n == m) → List (Fin n) → t₁ ⟷₁^ t₂
list2normI {t₁ = t₁} {t₂ = t₂} idp l rewrite (U^-is-Singleton t₁ t₂) = list2norm l


list2norm++ : {t : U^ (S n)} → (l r : List (Fin n)) →
              list2norm {t = t} (l ++ r) ⟷₂^ list2norm {t = t} l ◎^ list2norm r
list2norm++ nil r = idl◎r^ -- id⟷₁^
list2norm++ ((fs , fp) :: xs) r = trans⟷₂^ (id⟷₂^ ⊡^ (list2norm++ xs r)) assoc◎l^ -- 

-- cox≈2pi : {t₁ t₂ : U^ (S (S m))} → {r₁ r₂ : List (Fin (S m))} → r₁ ≈₁ r₂ → list2norm {t₁ = t₁} {t₂ = t₂} r₁ ⟷₂^ list2norm {t₁ = t₁} {t₂ = t₂} r₂
-- cox≈2pi {t₁ = I+ I+ t₁} {t₂ = I+ I+ t₂} (cancel {n}) =
--   transpos2pi n ◎^ transpos2pi n ◎^ id⟷₁^
--     ⟷₂^⟨ assoc◎l^ ⟩
--   (transpos2pi n ◎^ transpos2pi n) ◎^ id⟷₁^
--     ⟷₂^⟨ ? ⊡^ id⟷₂^ ⟩ -- transpos-cancel
--   id⟷₁^ ◎^ id⟷₁^
--     ⟷₂^⟨ idl◎l^ ⟩
--   id⟷₁^ ⟷₂^∎
-- cox≈2pi (swap {n} {k} lp) =
--   trans⟷₂^ assoc◎l^ (trans⟷₂^ ? assoc◎r^) -- (slide-transpos n k lp ⊡^ id⟷₂^)
-- cox≈2pi idp = id⟷₂^
-- cox≈2pi (comm rw) = !⟷₂^ (cox≈2pi rw)
-- cox≈2pi (trans rw₁ rw₂) = trans⟷₂^ (cox≈2pi rw₁) (cox≈2pi rw₂)
-- cox≈2pi (respects-++ {l} {l'} {r} {r'} rw₁ rw₂) =
--   trans⟷₂^
--     (list2norm++ l r)
--     (trans⟷₂^
--       ((cox≈2pi rw₁) ⊡^ (cox≈2pi rw₂))
--       (!⟷₂^ (list2norm++ l' r')))
-- cox≈2pi (braid {n}) =
--   trans⟷₂^ assoc◎l^
--   (trans⟷₂^ assoc◎l^
--   (trans⟷₂^ (assoc◎r^ ⊡^ id⟷₂^)
--   (trans⟷₂^ (braid-transpos n ⊡^ id⟷₂^)
--   (trans⟷₂^ (assoc◎l^ ⊡^ id⟷₂^)
  -- (trans⟷₂^ assoc◎r^ assoc◎r^)))))

piRespectsCox : {t₁ : U^ (S n)} {t₂ : U^ (S m)} → (p : n == m) → (l₁ l₂ : List (Fin n)) → (l₁ ≈ l₂) →
                (list2normI {t₁ = t₁} {t₂ = t₂} p l₁) ⟷₂^ (list2normI {t₁ = t₁} {t₂ = t₂} p l₂)
piRespectsCox {O} idp nil nil unit = id⟷₂^
piRespectsCox {S n} idp l₁ l₂ eq = TODO -- cox≈2pi eq

-- Mapping from combinators to lists

-- c2list : {t₁ t₂ : U} → (c : t₁ ⟷₁ t₂) →
--   Σ (List (Fin ∣ t₁ ∣)) (λ ns → (!⟷₁ (normC t₁) ◎^ c ◎ normC t₂) ⟷₂ list2norm ns)
-- c2list = ?

ℕ-S-is-inj-idp : {n : ℕ} -> ℕ-S-is-inj (S n) (S n) idp == idp
ℕ-S-is-inj-idp = prop-has-all-paths {{has-level-apply ℕ-level _ _}} _ _

norm2list : {t₁ : U^ (S n)} {t₂ : U^ m} → t₁ ⟷₁^ t₂ → List (Fin n)
norm2list swap₊^ = fzero :: nil
norm2list id⟷₁^ = nil
norm2list (_◎^_ {.(S _)} {_} {O} c₁ c₂) = nil
norm2list (_◎^_ {.(S _)} {_} {S o} c₁ c₂) = (norm2list c₁) ++ transport (λ e -> List (Fin e)) (ℕ-S-is-inj _ _ (! (⟷₁^-eq-size c₁))) (norm2list c₂)
norm2list {n = O} (⊕^ c) = nil
norm2list {n = S n} (⊕^ c) = map S⟨_⟩ (norm2list c)


-- -- Back and forth identities

norm2norm : {t₁ : U^ (S n)} {t₂ : U^ (S m)} → (c : t₁ ⟷₁^ t₂) →
    (list2normI {t₁ = t₁} {t₂ = t₂} (ℕ-S-is-inj _ _ (⟷₁^-eq-size c)) (norm2list c)) ⟷₂^ c
norm2norm (swap₊^ {t = t}) = TODO
norm2norm id⟷₁^ = TODO
norm2norm (_◎^_ {.(S _)} {_} {O} c₁ c₂) = TODO -- impossible
norm2norm (_◎^_ {.(S _)} {_} {S o} c₁ c₂) =
  let r1 = norm2norm c₁ 
      r2 = norm2norm c₂
  in  TODO
norm2norm {n = O} (⊕^ c) = TODO -- zero case
norm2norm {n = S n} (⊕^ c) = TODO
  -- let rec = norm2norm c
  -- in  TODO

list2list : {n : ℕ} → (p : List (Fin n)) → 
  norm2list {t₁ = quoteNorm₀ (pFin _)} {t₂ = quoteNorm₀ (pFin _)} (list2normI {t₁ = quoteNorm₀ (pFin _)} {t₂ = quoteNorm₀ (pFin _)} idp p) == p
list2list nil = TODO
list2list {S n} ((O , fp) :: ns) = TODO
  -- let rec = list2list ns
  --     n2n = norm2list (list2norm ns)
  --     tt = transport (λ e → List (Fin e)) (ℕ-S-is-inj (S n) (S n) idp) n2n == transport (λ e → List (Fin e)) idp n2n
  --     tt = ap (λ x → transport (λ e → List (Fin e)) x n2n) ℕ-S-is-inj-idp
  -- in  List=-out ((Fin= _ _ idp (O<S n) fp) , (tt ∙ rec))
list2list {S n} ((S x , fp) :: ns) = TODO

-- -----------------------------------------------------------------------------

