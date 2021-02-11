{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Indexed.Level0Norm where

open import lib.Base
open import lib.PathGroupoid
open import lib.types.Nat renaming (_+_ to _+ℕ_)
open import lib.types.Sigma
open import lib.types.Fin
open import lib.types.List
open import lib.NType

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxNorm as Pi^
open import Pi+.Misc

open import Pi+.Common.FinHelpers
open import Pi+.Coxeter.Coxeter
open import Pi+.Coxeter.Sn

private
  variable
    n m : ℕ

i^ : (n : ℕ) -> U^ n
i^ O = O
i^ (S n) = I+ i^ n

transpos2pi : {m : ℕ} -> (Fin m) -> (i^ (S m)) ⟷₁^ (i^ (S m))
transpos2pi {S m} (O , lp) = swap₊^
transpos2pi {S m} (S x , lp) = ⊕^ transpos2pi (x , (<-cancel-S lp))

transpos-cancel : {m : ℕ} {n : Fin (S m)} →
                  transpos2pi n ◎^ transpos2pi n ⟷₂^ id⟷₁^
transpos-cancel {m} {n} = {!   !}

slide0-transpos : {m : ℕ}  {kp : 0 < S (S (S m))} →
                  (n : Fin (S (S (S m)))) → (1<n : 1 < fst n) →
  transpos2pi n ◎^ transpos2pi (0 , kp) ⟷₂^ transpos2pi (0 , kp) ◎^ transpos2pi n
slide0-transpos = {!   !}

slide-transpos : {m : ℕ} → (n k : Fin (S m)) → (Sk<n : S (fst k) < fst n) →
  transpos2pi n ◎^ transpos2pi k ⟷₂^ transpos2pi k ◎^ transpos2pi n
slide-transpos {O} (.(S (S k)) , ltSR ()) (k , kp) ltS
slide-transpos {O} (.(S _) , ltSR ()) (k , kp) (ltSR lp)
slide-transpos {S O} (.(S (S k)) , ltSR (ltSR ())) (k , kp) ltS
slide-transpos {S O} (.(S _) , ltSR (ltSR ())) (k , p) (ltSR lp)
slide-transpos {S (S m)} n (O , kp) lp = slide0-transpos {kp = kp} n lp
slide-transpos {S (S m)} (S O , np) (S k , kp) (ltSR ())
slide-transpos {S (S m)} (S (S O) , np) (S k , kp) (ltSR (ltSR ()))
slide-transpos {S (S m)} (S (S (S n)) , np) (S k , kp) lp =
  let rn0 = transpos2pi (S (S n) , <-cancel-S np)
      rk0 = transpos2pi (k , <-cancel-S kp)
  in transpos2pi (S (S (S n)) , np) ◎^ transpos2pi (S k , kp)
       ⟷₂^⟨ id⟷₂^ ⟩
     (⊕^ rn0) ◎^ (⊕^ rk0)
       ⟷₂^⟨ hom◎⊕⟷₂^ ⟩
     ⊕^ (rn0 ◎^ rk0)
       ⟷₂^⟨ resp⊕⟷₂ 
         (slide-transpos (S (S n) , <-cancel-S np) (k , <-cancel-S kp) (<-cancel-S lp))  ⟩
     ⊕^ (rk0 ◎^ rn0)
       ⟷₂^⟨ hom⊕◎⟷₂^ ⟩
     (⊕^ rk0) ◎^ (⊕^ rn0)
       ⟷₂^⟨ id⟷₂^ ⟩
     transpos2pi (S k , kp) ◎^ transpos2pi (S (S (S n)) , np)
       ⟷₂^∎


braid-transpos : {m : ℕ} → (n : Fin m) →
  transpos2pi S⟨ n ⟩ ◎^ transpos2pi ⟨ n ⟩ ◎^ transpos2pi S⟨ n ⟩ ⟷₂^
  transpos2pi ⟨ n ⟩ ◎^ transpos2pi S⟨ n ⟩ ◎^ transpos2pi ⟨ n ⟩
braid-transpos {m} n = {!   !}

-- -- Mapping the entire list of transpositions to a combinator and
-- -- some properties

list2norm : {n m : ℕ} → (n == m) → {t₁ : U^ (S n)} {t₂ : U^ (S m)} → List (Fin n) → t₁ ⟷₁^ t₂
list2norm idp nil = idf^ -- id⟷₁^
list2norm {n} idp {t₂ = t₂} (fn :: xs) = idf^ ◎^ (transpos2pi fn) ◎^ (list2norm idp {I+ i^ n} {t₂} xs) ◎^ idf^

list2norm++ : {n m : ℕ} → (p : n == m) → {t₁ : U^ (S n)} {t₂ : U^ (S m)} → (l r : List (Fin n)) →
              list2norm p {t₁} {t₂} (l ++ r) ⟷₂^ list2norm {!   !} {t₁} {t₂} l ◎^ list2norm {!   !} {t₁} {t₂} r
list2norm++ p nil r = idl◎r^
list2norm++ p (n :: l) r = {!   !} -- trans⟷₂^ (id⟷₂^ ⊡^ (list2norm++ l r)) assoc◎l^

-- cox≈2pi : {m : ℕ} {r₁ r₂ : List (Fin (S m))} → r₁ ≈₁ r₂ → list2norm r₁ ⟷₂^ list2norm r₂
-- cox≈2pi (cancel {n}) =
--   transpos2pi n ◎^ transpos2pi n ◎^ id⟷₁^
--     ⟷₂^⟨ assoc◎l^ ⟩
--   (transpos2pi n ◎^ transpos2pi n) ◎^ id⟷₁^
--     ⟷₂^⟨ transpos-cancel ⊡^ id⟷₂^ ⟩
--   id⟷₁^ ◎^ id⟷₁^
--     ⟷₂^⟨ idl◎l^ ⟩
--   id⟷₁^ ⟷₂^∎
-- cox≈2pi (swap {n} {k} lp) =
--   trans⟷₂^ assoc◎l^ (trans⟷₂^ (slide-transpos n k lp ⊡^ id⟷₂^) assoc◎r^)
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
--   (trans⟷₂^ assoc◎r^ assoc◎r^)))))

piRespectsCox : {n m : ℕ} → (p : n == m) → {t₁ : U^ (S n)} {t₂ : U^ (S m)} → (l₁ l₂ : List (Fin n)) → (l₁ ≈ l₂) →
                (list2norm p {t₁} {t₂} l₁) ⟷₂^ (list2norm p {t₁} {t₂} l₂)
piRespectsCox {O} idp nil nil unit = id⟷₂^
piRespectsCox {S n} idp l₁ l₂ eq = {! cox≈2pi eq  !} -- cox≈2pi eq

-- Mapping from combinators to lists

-- c2list : {t₁ t₂ : U} → (c : t₁ ⟷₁ t₂) →
--   Σ (List (Fin ∣ t₁ ∣)) (λ ns → (!⟷₁ (normC t₁) ◎^ c ◎ normC t₂) ⟷₂ list2norm ns)
-- c2list = ?


norm2list-h : {t₁ : U^ n} {t₂ : U^ m} → t₁ ⟷₁^ t₂ → List (Fin n)
norm2list-h swap₊^ = fzero :: nil
norm2list-h id⟷₁^ = nil
norm2list-h (c₁ ◎^ c₂) = (norm2list-h c₁) ++ transport (λ z → List (Fin z)) (! (⟷₁-eq-size c₁)) (norm2list-h c₂)
norm2list-h (⊕^ c) = map S⟨_⟩ (norm2list-h c)

norm2list : {t₁ : U^ (S n)} {t₂ : U^ (S m)} → t₁ ⟷₁^ t₂ → List (Fin n)
norm2list = {!  !}

-- -- Back and forth identities

norm2norm : {t₁ : U^ (S n)} {t₂ : U^ (S m)} → (c : t₁ ⟷₁^ t₂) → 
    (list2norm (ℕ-S-is-inj _ _ (⟷₁-eq-size c)) {t₁} {t₂} (norm2list c)) ⟷₂^ c
norm2norm c = {!  !}

list2list : {n : ℕ} → (p : List (Fin n)) → norm2list (list2norm idp {i^ (S n)} {i^ (S n)} p) == p
list2list ns = {!  !}

-----------------------------------------------------------------------------

