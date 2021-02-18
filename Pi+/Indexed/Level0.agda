{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.Indexed.Level0 where

open import lib.Base
open import lib.PathGroupoid
open import lib.types.Nat renaming (_+_ to _+ℕ_)
open import lib.types.Sigma
open import lib.types.Fin
open import lib.types.List
open import lib.NType

open import Pi+.Indexed.Syntax
open import Pi+.Misc
open import Pi+.Extra

open import Pi+.Common.FinHelpers
open import Pi+.Coxeter.Coxeter
open import Pi+.Coxeter.Sn

-----------------------------------------------------------------------------
-- Canonical representation of sum types as "lists" I + (I + (I + ... O))

private
  variable
    n m p : ℕ

∣_∣ : U n → ℕ
∣ O ∣ = 0
∣ I ∣ = 1
∣ t₁ + t₂ ∣ = ∣ t₁ ∣ +ℕ ∣ t₂ ∣

⟪_⟫ : (n : ℕ) → U n
⟪ O ⟫ = O
⟪ S n ⟫ = I + ⟪ n ⟫

canonU : U n → U n
canonU t = ⟪ _ ⟫

-- Append two lists of the form I + (I + ... O)
⟪++⟫ : {m n : ℕ} → ⟪ m ⟫ + ⟪ n ⟫ ⟷₁ ⟪ m +ℕ n ⟫
⟪++⟫ {O} = unite₊l
⟪++⟫ {S m} = assocr₊ ◎ (id⟷₁ ⊕ ⟪++⟫)

-- Flatten a Pi type (a tree) to a list
normC : (t : U n) → t ⟷₁ canonU t
normC O = id⟷₁
normC I  = uniti₊l ◎ swap₊
normC (t₁ + t₂) = (normC t₁ ⊕ normC t₂) ◎ ⟪++⟫

-----------------------------------------------------------------------------
-- Mapping betweem pi combinators over non-zero types to and from the
-- Coxeter representation

-- Mapping each transposition index to a combinator and
-- some properties

transpos2pi : {m : ℕ} → Fin m → ⟪ S m ⟫ ⟷₁ ⟪ S m ⟫
transpos2pi {S m} (O , lp) = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
transpos2pi {S m} (S fn , lp) = id⟷₁ ⊕ transpos2pi (fn , <-cancel-S lp)

transpos-cancel : {m : ℕ} {n : Fin (S m)} →
                  transpos2pi n ◎ transpos2pi n ⟷₂ id⟷₁
transpos-cancel {O} {.0 , ltS} =
  (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
    ⟷₂⟨ trans⟷₂
            assoc◎r
            (trans⟷₂
              (id⟷₂ ⊡ assoc◎r)
              (id⟷₂ ⊡ (id⟷₂ ⊡ assoc◎l))) ⟩
  (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ (assocr₊ ◎ assocl₊) ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
    ⟷₂⟨ trans⟷₂
           (id⟷₂ ⊡ (id⟷₂ ⊡ (linv◎l ⊡ id⟷₂)))
           (id⟷₂ ⊡ (id⟷₂ ⊡ idl◎l)) ⟩
  (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
    ⟷₂⟨ id⟷₂ ⊡ assoc◎l ⟩
  (assocl₊ ◎ ((swap₊ ⊕ id⟷₁) ◎ (swap₊ ⊕ id⟷₁)) ◎ assocr₊)
    ⟷₂⟨ trans⟷₂ (id⟷₂ ⊡ (linv◎l ⊡ id⟷₂)) (id⟷₂ ⊡ idl◎l)  ⟩
  (assocl₊ ◎ assocr₊)
    ⟷₂⟨ linv◎l ⟩
  id⟷₁ ⟷₂∎
transpos-cancel {S m} {O , lp} =
  (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
    ⟷₂⟨ trans⟷₂
            assoc◎r
            (trans⟷₂
              (id⟷₂ ⊡ assoc◎r)
              (id⟷₂ ⊡ (id⟷₂ ⊡ assoc◎l))) ⟩
  (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ (assocr₊ ◎ assocl₊) ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
    ⟷₂⟨ trans⟷₂
           (id⟷₂ ⊡ (id⟷₂ ⊡ (linv◎l ⊡ id⟷₂)))
           (id⟷₂ ⊡ (id⟷₂ ⊡ idl◎l)) ⟩
  (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
    ⟷₂⟨ id⟷₂ ⊡ assoc◎l ⟩
  (assocl₊ ◎ ((swap₊ ⊕ id⟷₁) ◎ (swap₊ ⊕ id⟷₁)) ◎ assocr₊)
    ⟷₂⟨ trans⟷₂ (id⟷₂ ⊡ (linv◎l ⊡ id⟷₂)) (id⟷₂ ⊡ idl◎l)  ⟩
  (assocl₊ ◎ assocr₊)
    ⟷₂⟨ linv◎l ⟩
  id⟷₁ ⟷₂∎
transpos-cancel {S m} {S n , lp} =
  trans⟷₂
    hom◎⊕⟷₂
    (trans⟷₂ (resp⊕⟷₂ idl◎l transpos-cancel) id⟷₁⊕id⟷₁⟷₂)

slide0-transpos : {m : ℕ}  {kp : 0 < S (S (S m))} →
                  (n : Fin (S (S (S m)))) → (1<n : 1 < fst n) →
  transpos2pi n ◎ transpos2pi (0 , kp) ⟷₂ transpos2pi (0 , kp) ◎ transpos2pi n
slide0-transpos (S O , np) (ltSR ())
slide0-transpos (S (S n) , np) lp =
  let tr0 = transpos2pi (n , <-cancel-S (<-cancel-S np))
  in (id⟷₁ ⊕ (id⟷₁ ⊕ tr0)) ◎ (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
       ⟷₂⟨ trans⟷₂ assoc◎l (assocl₊l ⊡ id⟷₂) ⟩
     (assocl₊ ◎ ((id⟷₁ ⊕ id⟷₁) ⊕ tr0)) ◎ ((swap₊ ⊕ id⟷₁) ◎ assocr₊)
       ⟷₂⟨ assoc◎r ⟩
     assocl₊ ◎ ((id⟷₁ ⊕ id⟷₁) ⊕ tr0) ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
       ⟷₂⟨ id⟷₂ ⊡ (trans⟷₂ (resp⊕⟷₂ id⟷₁⊕id⟷₁⟷₂ id⟷₂ ⊡ id⟷₂) assoc◎l)  ⟩
     assocl₊ ◎ ((id⟷₁ ⊕ tr0) ◎ (swap₊ ⊕ id⟷₁)) ◎ assocr₊
       ⟷₂⟨ id⟷₂ ⊡ (hom◎⊕⟷₂ ⊡ id⟷₂)  ⟩
     assocl₊ ◎ ((id⟷₁ ◎ swap₊) ⊕ (tr0 ◎ id⟷₁)) ◎ assocr₊
       ⟷₂⟨ id⟷₂ ⊡ (trans⟷₂ (resp⊕⟷₂ idl◎l idr◎l) (resp⊕⟷₂ idr◎r idl◎r) ⊡ id⟷₂) ⟩
     assocl₊ ◎ ((swap₊ ◎ id⟷₁) ⊕ (id⟷₁ ◎ tr0)) ◎ assocr₊
       ⟷₂⟨  id⟷₂ ⊡ (hom⊕◎⟷₂ ⊡ id⟷₂)  ⟩
     assocl₊ ◎ ((swap₊ ⊕ id⟷₁) ◎ (id⟷₁ ⊕ tr0)) ◎ assocr₊
       ⟷₂⟨ id⟷₂ ⊡ ((id⟷₂ ⊡ resp⊕⟷₂ split⊕-id⟷₁ id⟷₂) ⊡ id⟷₂) ⟩
     assocl₊ ◎ ((swap₊ ⊕ id⟷₁) ◎ ((id⟷₁ ⊕ id⟷₁) ⊕ tr0)) ◎ assocr₊
       ⟷₂⟨ id⟷₂ ⊡ trans⟷₂ assoc◎r (id⟷₂ ⊡ assocr₊r) ⟩
     assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊ ◎ (id⟷₁ ⊕ (id⟷₁ ⊕ tr0))
       ⟷₂⟨ trans⟷₂ (id⟷₂ ⊡ assoc◎l) assoc◎l ⟩
     (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ (id⟷₁ ⊕ (id⟷₁ ⊕ tr0)) ⟷₂∎

slide-transpos : {m : ℕ} → (n k : Fin (S m)) → (Sk<n : S (fst k) < fst n) →
  transpos2pi n ◎ transpos2pi k ⟷₂ transpos2pi k ◎ transpos2pi n
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
  in transpos2pi (S (S (S n)) , np) ◎ transpos2pi (S k , kp)
       ⟷₂⟨ id⟷₂ ⟩
     (id⟷₁ ⊕ rn0) ◎ (id⟷₁ ⊕ rk0)
       ⟷₂⟨ hom◎⊕⟷₂ ⟩
     (id⟷₁ ◎ id⟷₁) ⊕ (rn0 ◎ rk0)
       ⟷₂⟨ resp⊕⟷₂ id⟷₂
         (slide-transpos (S (S n) , <-cancel-S np) (k , <-cancel-S kp) (<-cancel-S lp))  ⟩
     (id⟷₁ ◎ id⟷₁) ⊕ (rk0 ◎ rn0)
       ⟷₂⟨ hom⊕◎⟷₂ ⟩
     (id⟷₁ ⊕ rk0) ◎ (id⟷₁ ⊕ rn0)
       ⟷₂⟨ id⟷₂ ⟩
     transpos2pi (S k , kp) ◎ transpos2pi (S (S (S n)) , np) ⟷₂∎

braid-transpos : {m : ℕ} → (n : Fin m) →
  transpos2pi S⟨ n ⟩ ◎ transpos2pi ⟨ n ⟩ ◎ transpos2pi S⟨ n ⟩ ⟷₂
  transpos2pi ⟨ n ⟩ ◎ transpos2pi S⟨ n ⟩ ◎ transpos2pi ⟨ n ⟩
braid-transpos {S m} (O , np) =
  let rp0  = assocl₊ {t₁ = I} {t₂ = I} {t₃ = ⟪ m ⟫} ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
      rpn0 = assocl₊ {t₁ = I} {t₂ = I} {t₃ = I + ⟪ m ⟫} ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
  in
    transpos2pi S⟨ O , np ⟩ ◎ transpos2pi ⟨ O , np ⟩ ◎ transpos2pi S⟨ O , np ⟩
      ⟷₂⟨ id⟷₂ ⟩
    (id⟷₁ ⊕ rp0) ◎ rpn0 ◎ (id⟷₁ ⊕ rp0)
      ⟷₂⟨ TODO ⟩
    rpn0 ◎ (id⟷₁ ⊕ rp0) ◎ rpn0
      ⟷₂⟨ id⟷₂ ⟩
    transpos2pi ⟨ O , np ⟩ ◎ transpos2pi S⟨ O , np ⟩ ◎ transpos2pi ⟨ O , np ⟩ ⟷₂∎
braid-transpos {S m} (S n , np) =
  let t1 = transport2 (λ e f ->
              ((id⟷₁ ◎ id⟷₁ ◎ id⟷₁) ⊕
              (id⟷₁ ⊕ transpos2pi (n , <-cancel-S e)) ◎
              transpos2pi (n , f) ◎
              id⟷₁ ⊕ transpos2pi (n , <-cancel-S e))
              ⟷₂
              ((id⟷₁ ◎ id⟷₁ ◎ id⟷₁) ⊕
              (id⟷₁ ⊕ transpos2pi (n , <-cancel-S (<-ap-S (<-cancel-S np)))) ◎
              transpos2pi (n , ltSR (<-cancel-S np)) ◎
              id⟷₁ ⊕ transpos2pi (n , <-cancel-S (<-ap-S (<-cancel-S np)))))
           (<-has-all-paths (<-ap-S (<-cancel-S np)) (<-cancel-S (<-ap-S np)))
           (<-has-all-paths (ltSR (<-cancel-S np)) (<-trans ltS np))
           id⟷₂
      t2 = transport2 (λ e f ->
              (_⊕_ {1} {I} {1} {I} (id⟷₁ ◎ id⟷₁ ◎ id⟷₁)
              (transpos2pi (n , e) ◎
              (id⟷₁ ⊕ transpos2pi (n , f)) ◎
              transpos2pi (n , e)))
              ⟷₂
              ((id⟷₁ ◎ id⟷₁ ◎ id⟷₁) ⊕
              transpos2pi (n , <-trans ltS np) ◎
              (id⟷₁ ⊕ transpos2pi (n , <-cancel-S (<-cancel-S (<-ap-S np)))) ◎
              transpos2pi (n , <-trans ltS np)))
            (<-has-all-paths (<-trans ltS np) (ltSR (<-cancel-S np)))
            (<-has-all-paths (<-cancel-S (<-cancel-S (<-ap-S np)))
            (<-cancel-S (<-ap-S (<-cancel-S np)))) id⟷₂
  in
    transpos2pi S⟨ S n , np ⟩ ◎ transpos2pi ⟨ S n , np ⟩ ◎ transpos2pi S⟨ S n , np ⟩
      ⟷₂⟨ id⟷₂ ⊡ hom◎⊕⟷₂ ⟩
    (id⟷₁ ⊕ transpos2pi (S n , <-cancel-S (<-ap-S np))) ◎
      ((id⟷₁ ◎ id⟷₁) ⊕
      (transpos2pi (n , <-cancel-S (ltSR np)) ◎ transpos2pi (S n , <-cancel-S (<-ap-S np))))
      ⟷₂⟨ hom◎⊕⟷₂ ⟩
    ((id⟷₁ ◎ (id⟷₁ ◎ id⟷₁)) ⊕
    (transpos2pi (S n , <-cancel-S (<-ap-S np)) ◎
    (transpos2pi (n , <-cancel-S (ltSR np)) ◎ transpos2pi (S n , <-cancel-S (<-ap-S np)))))
      ⟷₂⟨ t1 ⟩
    ((id⟷₁ ◎ (id⟷₁ ◎ id⟷₁)) ⊕
    (transpos2pi (S n , <-ap-S (<-cancel-S np)) ◎
    (transpos2pi (n , ltSR (<-cancel-S np)) ◎ transpos2pi (S n , <-ap-S (<-cancel-S np)))))
      ⟷₂⟨ resp⊕⟷₂ id⟷₂ (braid-transpos (n , <-cancel-S np)) ⟩
    ((id⟷₁ ◎ (id⟷₁ ◎ id⟷₁)) ⊕
      (transpos2pi (n , ltSR (<-cancel-S np)) ◎
        transpos2pi (S n , <-ap-S (<-cancel-S np)) ◎
        transpos2pi (n , ltSR (<-cancel-S np))))
      ⟷₂⟨ t2 ⟩
    (id⟷₁ ◎ (id⟷₁ ◎ id⟷₁)) ⊕
    (transpos2pi (n , <-cancel-S (ltSR np)) ◎
      (transpos2pi (S n , <-cancel-S (<-ap-S np)) ◎
      (transpos2pi (n , <-cancel-S (ltSR np)))))
      ⟷₂⟨ hom⊕◎⟷₂ ⟩
    (id⟷₁ ⊕ transpos2pi (n , <-cancel-S (ltSR np))) ◎
      ((id⟷₁ ◎ id⟷₁) ⊕
      (transpos2pi (S n , <-cancel-S (<-ap-S np)) ◎
      (transpos2pi (n , <-cancel-S (ltSR np)))))
      ⟷₂⟨ id⟷₂ ⊡ hom⊕◎⟷₂ ⟩
    (transpos2pi ⟨ S n , np ⟩ ◎ transpos2pi S⟨ S n , np ⟩ ◎ transpos2pi ⟨ S n , np ⟩) ⟷₂∎

-- Mapping the entire list of transpositions to a combinator and
-- some properties

list2norm : {m : ℕ} → List (Fin m) → ⟪ S m ⟫ ⟷₁ ⟪ S m ⟫
list2norm nil = id⟷₁
list2norm (fn :: xs) = transpos2pi fn ◎ list2norm xs

list2norm++ : {m : ℕ} → (l r : List (Fin (S m))) →
              list2norm (l ++ r) ⟷₂ list2norm l ◎ list2norm r
list2norm++ nil r = idl◎r
list2norm++ (n :: l) r = trans⟷₂ (id⟷₂ ⊡ (list2norm++ l r)) assoc◎l

cox≈2pi : {m : ℕ} {r₁ r₂ : List (Fin (S m))} → r₁ ≈₁ r₂ → list2norm r₁ ⟷₂ list2norm r₂
cox≈2pi (cancel {n}) =
  transpos2pi n ◎ transpos2pi n ◎ id⟷₁
    ⟷₂⟨ assoc◎l ⟩
  (transpos2pi n ◎ transpos2pi n) ◎ id⟷₁
    ⟷₂⟨ transpos-cancel ⊡ id⟷₂ ⟩
  id⟷₁ ◎ id⟷₁
    ⟷₂⟨ idl◎l ⟩
  id⟷₁ ⟷₂∎
cox≈2pi (swap {n} {k} lp) =
  trans⟷₂ assoc◎l (trans⟷₂ (slide-transpos n k lp ⊡ id⟷₂) assoc◎r)
cox≈2pi idp = id⟷₂
cox≈2pi (comm rw) = !⟷₂ (cox≈2pi rw)
cox≈2pi (trans rw₁ rw₂) = trans⟷₂ (cox≈2pi rw₁) (cox≈2pi rw₂)
cox≈2pi (respects-++ {l} {l'} {r} {r'} rw₁ rw₂) =
  trans⟷₂
    (list2norm++ l r)
    (trans⟷₂
      ((cox≈2pi rw₁) ⊡ (cox≈2pi rw₂))
      (!⟷₂ (list2norm++ l' r')))
cox≈2pi (braid {n}) =
  trans⟷₂ assoc◎l
  (trans⟷₂ assoc◎l
  (trans⟷₂ (assoc◎r ⊡ id⟷₂)
  (trans⟷₂ (braid-transpos n ⊡ id⟷₂)
  (trans⟷₂ (assoc◎l ⊡ id⟷₂)
  (trans⟷₂ assoc◎r assoc◎r)))))

piRespectsCox : (n : ℕ) → (l₁ l₂ : List (Fin n)) → (l₁ ≈ l₂) →
                (list2norm l₁) ⟷₂ (list2norm l₂)
piRespectsCox O nil nil unit = id⟷₂
piRespectsCox (S n) l₁ l₂ eq = cox≈2pi eq

-----------------------------------------------------------------------------

