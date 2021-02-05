{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Level0 where

open import lib.Base
open import lib.PathGroupoid
open import lib.types.Nat renaming (_+_ to _+ℕ_)
open import lib.types.Sigma
open import lib.types.Fin
open import lib.types.List
open import lib.NType

open import Pi+.Syntax
open import Pi+.Misc

open import Pi+.Coxeter.Parametrized.ReductionRel
open import Pi+.Coxeter.Parametrized.Coxeter
open import Pi+.Coxeter.Parametrized.Group

-----------------------------------------------------------------------------
-- Canonical representation of sum types as "lists" I + (I + (I + ... O))

∣_∣ : U → ℕ
∣ O ∣ = 0
∣ I ∣ = 1
∣ t₁ + t₂ ∣ = ∣ t₁ ∣ +ℕ ∣ t₂ ∣

⟪_⟫ : ℕ → U
⟪ O ⟫ = O
⟪ S n ⟫ = I + ⟪ n ⟫

canonU : U → U
canonU t = ⟪ ∣ t ∣ ⟫

-----------------------------------------------------------------------------
-- Recovering a pi combinator over zero types from the
-- Coxeter representation

plus0l : (m n : ℕ) → (m +ℕ n == 0) → (m == 0)
plus0l O n pr = idp

plus0r : (m n : ℕ) → (m +ℕ n == 0) → (n == 0)
plus0r O n pr = pr

eqsize : {t₁ t₂ : U} → (p : t₁ ⟷₁ t₂) → ∣ t₁ ∣ == ∣ t₂ ∣
eqsize unite₊l = idp
eqsize uniti₊l = idp
eqsize (swap₊ {t₁} {t₂}) = +-comm ∣ t₁ ∣ ∣ t₂ ∣
eqsize (assocl₊ {t₁} {t₂} {t₃}) = ! (+-assoc (∣ t₁ ∣) (∣ t₂ ∣) (∣ t₃ ∣))
eqsize (assocr₊ {t₁} {t₂} {t₃}) = (+-assoc (∣ t₁ ∣) (∣ t₂ ∣) (∣ t₃ ∣))
eqsize id⟷₁ = idp
eqsize (p₁ ◎ p₂) = eqsize p₁ ∙ eqsize p₂
eqsize (p₁ ⊕ p₂) = ap2 (λ X Y → X +ℕ Y) (eqsize p₁) (eqsize p₂)

zeroDecompose : (t : U) → (tz : ∣ t ∣ == 0) →
                (t == O ⊎ Σ U (λ t' → (t ⟷₁ O + t') × (∣ t' ∣ == 0)))
zeroDecompose O idp = inj₁ idp
zeroDecompose (t₁ + t₂) tz with zeroDecompose t₁ (plus0l ∣ t₁ ∣ ∣ t₂ ∣ tz)
... | inj₁ idp = inj₂ (t₂ , id⟷₁ , tz)
... | inj₂ (t₃ , t₁⟷0+t₃ , t₃z) =
  inj₂ ((t₃ + t₂) ,
        ((t₁⟷0+t₃ ⊕ id⟷₁) ◎ assocr₊) ,
        ap2 (λ X Y → X +ℕ Y) t₃z (plus0r ∣ t₁ ∣ ∣ t₂ ∣ tz))

tzO : (t : U) → (tz : ∣ t ∣ == 0) → (t ⟷₁ O)
tzO O idp = id⟷₁
tzO (t₁ + t₂) tz =
  (tzO t₁ (plus0l ∣ t₁ ∣ ∣ t₂ ∣ tz) ⊕ tzO t₂ (plus0r ∣ t₁ ∣ ∣ t₂ ∣ tz)) ◎ unite₊l

-- instances don't resolve
tz0=l : {t : U} → {p1 : ∣ t ∣ == 0} → {p2 : ∣ t ∣ == 0} → (tzO t p1) ◎ (!⟷₁ (tzO t p2)) ⟷₂ id⟷₁
tz0=l {t} {p1} {p2} = transport (λ e -> ((tzO t p1) ◎ !⟷₁ (tzO t e)) ⟷₂ id⟷₁) (prop-has-all-paths {{has-level-apply-instance}} p1 p2) linv◎l

tz0=r : {t : U} → {p1 : ∣ t ∣ == 0} → {p2 : ∣ t ∣ == 0} → !⟷₁ (tzO t p1) ◎ (tzO t p2) ⟷₂ id⟷₁
tz0=r {t} {p1} {p2} = transport (λ e -> (!⟷₁ (tzO t p1) ◎ (tzO t e)) ⟷₂ id⟷₁) (prop-has-all-paths {{has-level-apply-instance}} p1 p2) rinv◎l

u-swap-u : uniti₊l ◎ swap₊ ◎ unite₊l ⟷₂ id⟷₁
u-swap-u = {!   !}

neg2 : {t₁ t₂ : U} -> (c₁ c₂ : t₁ ⟷₁ t₂) -> (c₁ ⟷₂ c₂) -> (!⟷₁ c₁ ⟷₂ !⟷₁ c₂)
neg2 .(_ ◎ _ ◎ _) .((_ ◎ _) ◎ _) assoc◎l = assoc◎r
neg2 .((_ ◎ _) ◎ _) .(_ ◎ _ ◎ _) assoc◎r = assoc◎l
neg2 .((_ ⊕ _ ⊕ _) ◎ assocl₊) .(assocl₊ ◎ (_ ⊕ _) ⊕ _) assocl₊l = assocr₊l
neg2 .(assocl₊ ◎ (_ ⊕ _) ⊕ _) .((_ ⊕ _ ⊕ _) ◎ assocl₊) assocl₊r = assocr₊r
neg2 .(((_ ⊕ _) ⊕ _) ◎ assocr₊) .(assocr₊ ◎ _ ⊕ _ ⊕ _) assocr₊r = assocl₊r
neg2 .(assocr₊ ◎ _ ⊕ _ ⊕ _) .(((_ ⊕ _) ⊕ _) ◎ assocr₊) assocr₊l = assocl₊l
neg2 .(id⟷₁ ◎ c₂) c₂ idl◎l = idr◎l
neg2 c₁ .(id⟷₁ ◎ c₁) idl◎r = idr◎r
neg2 .(c₂ ◎ id⟷₁) c₂ idr◎l = idl◎l
neg2 c₁ .(c₁ ◎ id⟷₁) idr◎r = idl◎r
neg2 .(_ ◎ !⟷₁ _) .id⟷₁ linv◎l = rinv◎l
neg2 .id⟷₁ .(_ ◎ !⟷₁ _) linv◎r = rinv◎r
neg2 .(!⟷₁ _ ◎ _) .id⟷₁ rinv◎l = linv◎l
neg2 .id⟷₁ .(!⟷₁ _ ◎ _) rinv◎r = linv◎r
neg2 .(unite₊l ◎ _) .((_ ⊕ _) ◎ unite₊l) unite₊l⟷₂l = uniti₊l⟷₂r
neg2 .((_ ⊕ _) ◎ unite₊l) .(unite₊l ◎ _) unite₊l⟷₂r = uniti₊l⟷₂l
neg2 .(uniti₊l ◎ _ ⊕ _) .(_ ◎ uniti₊l) uniti₊l⟷₂l = unite₊l⟷₂r
neg2 .(_ ◎ uniti₊l) .(uniti₊l ◎ _ ⊕ _) uniti₊l⟷₂r = unite₊l⟷₂l
neg2 .(swap₊ ◎ _ ⊕ _) .((_ ⊕ _) ◎ swap₊) swapl₊⟷₂ = swapr₊⟷₂
neg2 .((_ ⊕ _) ◎ swap₊) .(swap₊ ◎ _ ⊕ _) swapr₊⟷₂ = swapl₊⟷₂
neg2 c₁ .c₁ id⟷₂ = id⟷₂
neg2 c₁ c₂ (trans⟷₂ p₁ p₂) = trans⟷₂ (neg2 _ _ p₁) (neg2 _ _ p₂)
neg2 .(_ ◎ _) .(_ ◎ _) (p₁ ⊡ p₂) = neg2 _ _ p₂ ⊡ neg2 _ _ p₁
neg2 .(_ ⊕ _) .(_ ⊕ _) (resp⊕⟷₂ p₁ p₂) = resp⊕⟷₂ (neg2 _ _ p₁) (neg2 _ _ p₂)
neg2 .(id⟷₁ ⊕ id⟷₁) .id⟷₁ id⟷₁⊕id⟷₁⟷₂ = id⟷₁⊕id⟷₁⟷₂
neg2 .id⟷₁ .(id⟷₁ ⊕ id⟷₁) split⊕-id⟷₁ = split⊕-id⟷₁
neg2 .((_ ◎ _) ⊕ _ ◎ _) .((_ ⊕ _) ◎ _ ⊕ _) hom⊕◎⟷₂ = hom⊕◎⟷₂
neg2 .((_ ⊕ _) ◎ _ ⊕ _) .((_ ◎ _) ⊕ _ ◎ _) hom◎⊕⟷₂ = hom◎⊕⟷₂
neg2 .((swap₊ ◎ unite₊l) ⊕ id⟷₁) .(assocr₊ ◎ id⟷₁ ⊕ unite₊l) triangle₊l = {! -t 10  !}
neg2 .(assocr₊ ◎ id⟷₁ ⊕ unite₊l) .((swap₊ ◎ unite₊l) ⊕ id⟷₁) triangle₊r = {!   !}
neg2 .(assocr₊ ◎ assocr₊) .(((assocr₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁ ⊕ assocr₊) pentagon₊l = {! -t 30  !}
neg2 .(((assocr₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁ ⊕ assocr₊) .(assocr₊ ◎ assocr₊) pentagon₊r = {! -t 30  !}
neg2 .unite₊l .(swap₊ ◎ swap₊ ◎ unite₊l) unite₊l-coh-l = {! -t 30  !}
neg2 .(swap₊ ◎ swap₊ ◎ unite₊l) .unite₊l unite₊l-coh-r = {! -t 30  !}
neg2 .((assocr₊ ◎ swap₊) ◎ assocr₊) .(((swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁ ⊕ swap₊) hexagonr₊l = trans⟷₂ (trans⟷₂ assoc◎l hexagonl₊l) assoc◎r
neg2 .(((swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁ ⊕ swap₊) .((assocr₊ ◎ swap₊) ◎ assocr₊) hexagonr₊r = trans⟷₂ (trans⟷₂ assoc◎l hexagonl₊r) assoc◎r
neg2 .((assocl₊ ◎ swap₊) ◎ assocl₊) .(((id⟷₁ ⊕ swap₊) ◎ assocl₊) ◎ swap₊ ⊕ id⟷₁) hexagonl₊l = trans⟷₂ (trans⟷₂ assoc◎l hexagonr₊l) assoc◎r
neg2 .(((id⟷₁ ⊕ swap₊) ◎ assocl₊) ◎ swap₊ ⊕ id⟷₁) .((assocl₊ ◎ swap₊) ◎ assocl₊) hexagonl₊r = trans⟷₂ (trans⟷₂ assoc◎l hexagonr₊r) assoc◎r

gzero⟷₂ : (t₁ t₂ : U) → (t₁z : ∣ t₁ ∣ == 0) → (t₂z : ∣ t₂ ∣ == 0) → (c : t₁ ⟷₁ t₂) →
            (!⟷₁ (tzO t₁ t₁z) ◎ c ◎ (tzO t₂ t₂z)) ⟷₂ id⟷₁
gzero⟷₂ .(O + t₂) t₂ t₁z t₂z unite₊l = 
  let X1 = !⟷₁ (tzO t₂ t₁z)
      X2 = tzO t₂ t₂z
  in  ((uniti₊l ◎ (id⟷₁ ⊕ X1)) ◎ unite₊l ◎ X2) ⟷₂⟨ uniti₊l⟷₂l ⊡ id⟷₂ ⟩
      (X1 ◎ uniti₊l) ◎ unite₊l ◎ X2 ⟷₂⟨ assoc◎r ⟩
      X1 ◎ uniti₊l ◎ unite₊l ◎ X2 ⟷₂⟨ id⟷₂ ⊡ assoc◎l ⟩
      X1 ◎ (uniti₊l ◎ unite₊l) ◎ X2 ⟷₂⟨ id⟷₂ ⊡ (linv◎l ⊡ id⟷₂) ⟩
      X1 ◎ id⟷₁ ◎ X2 ⟷₂⟨ id⟷₂ ⊡ idl◎l ⟩
      X1 ◎ X2 ⟷₂⟨ tz0=r ⟩
      id⟷₁ ⟷₂∎
gzero⟷₂ t₁ .(O + t₁) t₁z t₂z uniti₊l = 
  let X1 = !⟷₁ (tzO t₁ t₁z)
      X2 = tzO t₁ t₂z
  in  (X1 ◎ uniti₊l ◎ (id⟷₁ ⊕ X2) ◎ unite₊l) ⟷₂⟨ id⟷₂ ⊡ (id⟷₂ ⊡ unite₊l⟷₂r) ⟩
      X1 ◎ uniti₊l ◎ unite₊l ◎ X2 ⟷₂⟨ id⟷₂ ⊡ assoc◎l ⟩
      X1 ◎ (uniti₊l ◎ unite₊l) ◎ X2 ⟷₂⟨ id⟷₂ ⊡ (linv◎l ⊡ id⟷₂) ⟩
      X1 ◎ id⟷₁ ◎ X2 ⟷₂⟨ id⟷₂ ⊡ idl◎l ⟩
      X1 ◎ X2 ⟷₂⟨ tz0=r ⟩
      id⟷₁ ⟷₂∎

gzero⟷₂ (t₁ + t₂) (t₂ + t₁) t₁z t₂z swap₊ = 
  let X2 = !⟷₁ (tzO _ (plus0l ∣ t₁ ∣ ∣ t₂ ∣ t₁z))
      X3 = !⟷₁ (tzO _ (plus0r ∣ t₁ ∣ ∣ t₂ ∣ t₁z))
      X5 = tzO _ (plus0l ∣ t₂ ∣ ∣ t₁ ∣ t₂z)
      X6 = tzO _ (plus0r ∣ t₂ ∣ ∣ t₁ ∣ t₂z)
  in  (uniti₊l ◎ (X2 ⊕ X3)) ◎ (swap₊ ◎ (X5 ⊕ X6) ◎ unite₊l) ⟷₂⟨ id⟷₂ ⊡ assoc◎l ⟩
      (uniti₊l ◎ (X2 ⊕ X3)) ◎ (swap₊ ◎ (X5 ⊕ X6)) ◎ unite₊l ⟷₂⟨ id⟷₂ ⊡ (swapl₊⟷₂ ⊡ id⟷₂) ⟩
      (uniti₊l ◎ (X2 ⊕ X3)) ◎ ((X6 ⊕ X5) ◎ swap₊) ◎ unite₊l ⟷₂⟨ id⟷₂ ⊡ assoc◎r ⟩
      (uniti₊l ◎ (X2 ⊕ X3)) ◎ (X6 ⊕ X5) ◎ swap₊ ◎ unite₊l ⟷₂⟨ assoc◎r ⟩
      uniti₊l ◎ (X2 ⊕ X3) ◎ (X6 ⊕ X5) ◎ swap₊ ◎ unite₊l ⟷₂⟨ id⟷₂ ⊡ assoc◎l ⟩
      uniti₊l ◎ ((X2 ⊕ X3) ◎ (X6 ⊕ X5)) ◎ swap₊ ◎ unite₊l ⟷₂⟨ id⟷₂ ⊡ (hom◎⊕⟷₂ ⊡ id⟷₂) ⟩
      uniti₊l ◎ ((X2 ◎ X6) ⊕ (X3 ◎ X5)) ◎ swap₊ ◎ unite₊l ⟷₂⟨ id⟷₂ ⊡ (resp⊕⟷₂ tz0=r tz0=r ⊡ id⟷₂) ⟩
      uniti₊l ◎ (id⟷₁ ⊕ id⟷₁) ◎ swap₊ ◎ unite₊l ⟷₂⟨ assoc◎l ⟩
      (uniti₊l ◎ (id⟷₁ ⊕ id⟷₁)) ◎ swap₊ ◎ unite₊l ⟷₂⟨ uniti₊l⟷₂l ⊡ id⟷₂ ⟩
      (id⟷₁ ◎ uniti₊l) ◎ swap₊ ◎ unite₊l ⟷₂⟨ trans⟷₂ assoc◎r idl◎l ⟩
      uniti₊l ◎ swap₊ ◎ unite₊l ⟷₂⟨ u-swap-u ⟩
      id⟷₁ ⟷₂∎
gzero⟷₂ (t₁ + t₂ + t₃) ((t₁ + t₂) + t₃) t₁z t₂z assocl₊ = 
  let X1 = !⟷₁ (tzO t₁ (plus0l ∣ t₁ ∣ (∣ t₂ ∣ +ℕ ∣ t₃ ∣) t₁z))
      X2 = !⟷₁ (tzO t₂ (plus0l ∣ t₂ ∣ ∣ t₃ ∣ (plus0r ∣ t₁ ∣ (∣ t₂ ∣ +ℕ ∣ t₃ ∣) t₁z)))
      X3 = !⟷₁ (tzO t₃ (plus0r ∣ t₂ ∣ ∣ t₃ ∣ (plus0r ∣ t₁ ∣ (∣ t₂ ∣ +ℕ ∣ t₃ ∣) t₁z)))
      X4 = tzO t₁ (plus0l ∣ t₁ ∣ ∣ t₂ ∣ (plus0l (∣ t₁ ∣ +ℕ ∣ t₂ ∣) ∣ t₃ ∣ t₂z))
      X5 = tzO t₂ (plus0r ∣ t₁ ∣ ∣ t₂ ∣ (plus0l (∣ t₁ ∣ +ℕ ∣ t₂ ∣) ∣ t₃ ∣ t₂z))
      X6 = tzO t₃ (plus0r (∣ t₁ ∣ +ℕ ∣ t₂ ∣) ∣ t₃ ∣ t₂z)
      -- doesn't really matter what are these combinators above
      -- just knowing that the assumptions below hold, it should
      -- be possible to prove the result
      X1∘X4 : X1 ◎ X4 ⟷₂ id⟷₁
      X1∘X4 = tz0=r
      X2∘X5 : X2 ◎ X5 ⟷₂ id⟷₁
      X2∘X5 = tz0=r
      X3∘X6 : X3 ◎ X6 ⟷₂ id⟷₁
      X3∘X6 = tz0=r
   in  (uniti₊l ◎ (X1 ⊕ uniti₊l ◎ (X2 ⊕ X3))) ◎ assocl₊ ◎ ((((X4 ⊕ X5) ◎ unite₊l) ⊕ X6) ◎ unite₊l) ⟷₂⟨ {!  !} ⟩
       id⟷₁ ⟷₂∎
gzero⟷₂ ((t₁ + t₂) + t₃) (t₁ + (t₂ + t₃)) t₁z t₂z assocr₊ = 
  let rec = gzero⟷₂ (t₁ + t₂ + t₃) ((t₁ + t₂) + t₃) t₂z t₁z assocl₊
      rec! = neg2 _ _ rec
      -- this should be just rec!, after filling in the hole above
  in  !⟷₁ ((((_ ⊕ _) ◎ unite₊l) ⊕ _) ◎ unite₊l) ◎ assocr₊ ◎ (_ ⊕ (_ ⊕ _) ◎ unite₊l) ◎ unite₊l ⟷₂⟨ {!  !} ⟩
       id⟷₁ ⟷₂∎
gzero⟷₂ t₁ .t₁ t₁z t₂z id⟷₁ = 
  trans⟷₂ (id⟷₂ ⊡ idl◎l) tz0=r
gzero⟷₂ t₁ t₂ t₁z t₂z (c ◎ c₁) = 
  let rec₁ = gzero⟷₂ _ _ t₁z (! (eqsize c) ∙ t₁z) c 
      rec₂ = gzero⟷₂ _ _ ((eqsize c₁) ∙ t₂z) t₂z c₁
      cc = rec₁ ⊡ rec₂
      X1 = !⟷₁ (tzO t₁ t₁z)
      X2 = c
      X3 = tzO _ (! (eqsize c) ∙ t₁z)
      X4 = !⟷₁ (tzO _ (eqsize c₁ ∙ t₂z))
      X5 = c₁
      X6 = tzO t₂ t₂z
  in  X1 ◎ (X2 ◎ X5) ◎ X6 ⟷₂⟨ id⟷₂ ⊡ assoc◎r ⟩
      X1 ◎ (X2 ◎ X5 ◎ X6) ⟷₂⟨ id⟷₂ ⊡ (id⟷₂ ⊡ !⟷₂ idl◎l) ⟩
      X1 ◎ (X2 ◎ id⟷₁ ◎ X5 ◎ X6) ⟷₂⟨ id⟷₂ ⊡ (id⟷₂ ⊡ (!⟷₂ tz0=l ⊡ id⟷₂)) ⟩
      X1 ◎ (X2 ◎ (X3 ◎ X4) ◎ X5 ◎ X6) ⟷₂⟨ id⟷₂ ⊡ (id⟷₂ ⊡ assoc◎r) ⟩
      X1 ◎ (X2 ◎ (X3 ◎ (X4 ◎ X5 ◎ X6))) ⟷₂⟨ id⟷₂ ⊡ assoc◎l ⟩
      (X1 ◎ ((X2 ◎ X3) ◎ (X4 ◎ X5 ◎ X6))) ⟷₂⟨ assoc◎l ⟩
      ((X1 ◎ X2 ◎ X3) ◎ (X4 ◎ X5 ◎ X6)) ⟷₂⟨ cc ⟩
      id⟷₁ ◎ id⟷₁ ⟷₂⟨ idl◎l ⟩
      id⟷₁ ⟷₂∎
gzero⟷₂ (t₁ + t₂) (t₃ + t₄) t₁z t₂z (c ⊕ c₁) = 
  let rec₁ = gzero⟷₂ _ _ (plus0l ∣ t₁ ∣ ∣ t₂ ∣ t₁z) (plus0l ∣ t₃ ∣ ∣ t₄ ∣ t₂z) c 
      rec₂ = gzero⟷₂ _ _ (plus0r ∣ t₁ ∣ ∣ t₂ ∣ t₁z) (plus0r ∣ t₃ ∣ ∣ t₄ ∣ t₂z) c₁
      cc = rec₁ ⊡ rec₂
      X1 = !⟷₁ (tzO t₁ (plus0l ∣ t₁ ∣ ∣ t₂ ∣ t₁z))
      X2 = !⟷₁ (tzO t₂ (plus0r ∣ t₁ ∣ ∣ t₂ ∣ t₁z))
      X3 = tzO t₃ (plus0l ∣ t₃ ∣ ∣ t₄ ∣ t₂z)
      X4 = tzO t₄ (plus0r ∣ t₃ ∣ ∣ t₄ ∣ t₂z)
  in  (uniti₊l ◎ (X1 ⊕ X2)) ◎ (c ⊕ c₁) ◎ ((X3 ⊕ X4) ◎ unite₊l) ⟷₂⟨ id⟷₂ ⊡ assoc◎l ⟩
      (uniti₊l ◎ (X1 ⊕ X2)) ◎ ((c ⊕ c₁) ◎ (X3 ⊕ X4)) ◎ unite₊l ⟷₂⟨ id⟷₂ ⊡ (hom◎⊕⟷₂ ⊡ id⟷₂) ⟩
      (uniti₊l ◎ (X1 ⊕ X2)) ◎ ((c ◎ X3) ⊕ (c₁ ◎ X4)) ◎ unite₊l ⟷₂⟨ assoc◎r ⟩
      uniti₊l ◎ (X1 ⊕ X2) ◎ ((c ◎ X3) ⊕ (c₁ ◎ X4)) ◎ unite₊l ⟷₂⟨ id⟷₂ ⊡ assoc◎l ⟩
      uniti₊l ◎ ((X1 ⊕ X2) ◎ ((c ◎ X3) ⊕ (c₁ ◎ X4))) ◎ unite₊l ⟷₂⟨ id⟷₂ ⊡ (hom◎⊕⟷₂ ⊡ id⟷₂) ⟩
      uniti₊l ◎ ((X1 ◎ c ◎ X3) ⊕ (X2 ◎ c₁ ◎ X4)) ◎ unite₊l ⟷₂⟨ id⟷₂ ⊡ ((resp⊕⟷₂ rec₁ rec₂) ⊡ id⟷₂) ⟩
      uniti₊l ◎ (id⟷₁ ⊕ id⟷₁) ◎ unite₊l ⟷₂⟨ id⟷₂ ⊡ (id⟷₁⊕id⟷₁⟷₂ ⊡ id⟷₂) ⟩
      uniti₊l ◎ id⟷₁ ◎ unite₊l ⟷₂⟨ id⟷₂ ⊡ idl◎l ⟩
      uniti₊l ◎ unite₊l ⟷₂⟨ linv◎l ⟩
      id⟷₁ ⟷₂∎

zero⟷₂ : (p : O ⟷₁ O) → (id⟷₁ ⟷₂ p)
zero⟷₂ id⟷₁ = id⟷₂
zero⟷₂ (_◎_ {O} {t} {O} p₁ p₂) with zeroDecompose t (eqsize p₂)
... | inj₁ idp = trans⟷₂ idl◎r ((zero⟷₂ p₁) ⊡ (zero⟷₂ p₂))
... | inj₂ (t₃ , p₃ , t₃z) = 
  let rec₁ = gzero⟷₂ O t idp (eqsize p₂) p₁
      rec₂ = gzero⟷₂ t O (eqsize p₂) idp p₂
      cc = rec₁ ⊡ rec₂
  in  !⟷₂ ( p₁ ◎ p₂ ⟷₂⟨ !⟷₂ (id⟷₂ ⊡ idl◎l) ⟩
            p₁ ◎ id⟷₁ ◎ p₂ ⟷₂⟨ !⟷₂ (id⟷₂ ⊡ (linv◎l ⊡ id⟷₂)) ⟩
            p₁ ◎ (tzO t (eqsize p₂) ◎ !⟷₁ (tzO t (eqsize p₂))) ◎ p₂ ⟷₂⟨ !⟷₂ (id⟷₂ ⊡ assoc◎l) ⟩
            p₁ ◎ tzO t (eqsize p₂) ◎ !⟷₁ (tzO t (eqsize p₂)) ◎ p₂ ⟷₂⟨ !⟷₂ assoc◎r ⟩
            (p₁ ◎ tzO t (eqsize p₂)) ◎ (!⟷₁ (tzO t (eqsize p₂)) ◎ p₂) ⟷₂⟨ !⟷₂ (idl◎l ⊡ trans⟷₂ assoc◎l idr◎l) ⟩
            _ ⟷₂⟨ cc ⟩
            id⟷₁ ◎ id⟷₁ ⟷₂⟨ idl◎l ⟩
            id⟷₁ ⟷₂∎
      )


{--
  O ---p1--- t ---p2--- 0
             |
             |
             |
           0 + t3

  ∣ t₃ ∣ == 0
--}

-----------------------------------------------------------------------------
-- Recovering a pi combinator over non-zero types from the
-- Coxeter representation

norm2list : {n : ℕ} → ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫ → List (Fin n)
norm2list p = {!!}

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
  let rp0  = assocl₊ {I} {I} {⟪ m ⟫} ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
      rpn0 = assocl₊ {I} {I} {I + ⟪ m ⟫} ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
  in
    transpos2pi S⟨ O , np ⟩ ◎ transpos2pi ⟨ O , np ⟩ ◎ transpos2pi S⟨ O , np ⟩
      ⟷₂⟨ id⟷₂ ⟩
    (id⟷₁ ⊕ rp0) ◎ rpn0 ◎ (id⟷₁ ⊕ rp0)
      ⟷₂⟨ {!!} ⟩
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
              (_⊕_ {I} {I + I + ⟪ m ⟫} {I} {I + I + ⟪ m ⟫} (id⟷₁ ◎ id⟷₁ ◎ id⟷₁)
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

-- Back and forth identities

norm2norm : {n : ℕ} → (p : ⟪ S n ⟫ ⟷₁ ⟪ S n ⟫) → list2norm (norm2list p) ⟷₂ p
norm2norm p = {!!}

list2list : {n : ℕ} → (p : List (Fin n)) → norm2list (list2norm p) == p
list2list ns = {!!}

-----------------------------------------------------------------------------


{--
-----------------------------------------------------------------------------
-- Canonical representation of sum types as lists I + (I + (I + ... O))

∣_∣ : U → ℕ
∣ O ∣ = 0
∣ I ∣ = 1
∣ t₁ + t₂ ∣ = ∣ t₁ ∣ +ℕ ∣ t₂ ∣

⟪_⟫ : ℕ → U
⟪ O ⟫ = O
⟪ S n ⟫ = I + ⟪ n ⟫

canonU : U → U
canonU t = ⟪ ∣ t ∣ ⟫

--

data UVec : (n : ℕ) → Set where
  [] : UVec 0
  X : {n : ℕ} → (nt : UVec n) → UVec (S n)

tail : {n : ℕ} → UVec (S n) → UVec n
tail (X nf) = nf

data SplitUVec : {i j : ℕ} → UVec i → UVec j → Set where
  here : {n : ℕ} {nf : UVec n} →
         SplitUVec [] nf
  skip : {i j : ℕ} {before : UVec i} {after : UVec (S j)} →
         SplitUVec (X before) (tail after)

⟦_⟧ : (n : ℕ) → UVec n
⟦ 0 ⟧ = []
⟦ S n ⟧ = X ⟦ n ⟧

nfU : (t : U) → UVec ∣ t ∣
nfU t = ⟦ ∣ t ∣ ⟧

nf→canon : {m : ℕ} → UVec m → U
nf→canon [] = O
nf→canon (X nf) = I + nf→canon nf
-}
-----------------------------------------------------------------------------
-- Converting Pi types to normal form

-- Append two lists of the form I + (I + ... O)
⟪++⟫ : {m n : ℕ} → ⟪ m ⟫ + ⟪ n ⟫ ⟷₁ ⟪ m +ℕ n ⟫
⟪++⟫ {O} = unite₊l
⟪++⟫ {S m} = assocr₊ ◎ (id⟷₁ ⊕ ⟪++⟫)

-- Flatten a Pi type (a tree) to a list
normC : (t : U) → t ⟷₁ canonU t
normC O = id⟷₁
normC I  = uniti₊l ◎ swap₊
normC (t₁ + t₂) = (normC t₁ ⊕ normC t₂) ◎ ⟪++⟫
{-
-----------------------------------------------------------------------------
-- Example

-- postulate A B C D E F : U
A B C D E F : U
A = I
B = I
C = I
D = I
E = I
F = I

tree eert : U
tree = ((A + B) + C) + ((D + E) + F)
eert = (F + (E + D)) + (C + (B + A))

-- canonU tree == A + (B + (C + (D + (E + (F + O)))))
-- canonU eert == F + (E + (D + (C + (B + (A + O)))))

-----------------------------------------------------------------------------
-- Special combinators on normal forms

-- Change to use SplitUVec...

data _⇔_ : (t₁ t₂ : U) → Set where
  id⇔ : {m : ℕ} → ⟪ m ⟫ ⇔ ⟪ m ⟫

  seq⇔ : {m n k : ℕ} → ⟪ m ⟫ ⇔ ⟪ n ⟫ → ⟪ n ⟫ ⇔ ⟪ k ⟫ → ⟪ m ⟫ ⇔ ⟪ k ⟫
  append⇔ : {m n k p : ℕ} → ⟪ m ⟫ ⇔ ⟪ k ⟫ → ⟪ n ⟫ ⇔ ⟪ p ⟫ →
            ⟪ m +ℕ n ⟫ ⇔ ⟪ k +ℕ p ⟫
  assocl⇔ : {m n k : ℕ} → ⟪ m +ℕ (n +ℕ k) ⟫ ⇔ ⟪ (m +ℕ n)  +ℕ k ⟫
  assocr⇔ : {m n k : ℕ} → ⟪ (m +ℕ n) +ℕ k ⟫ ⇔ ⟪ m +ℕ (n +ℕ k) ⟫
  snocN⇔ : {m : ℕ} → ⟪ 1 +ℕ m ⟫ ⇔ ⟪ m +ℕ 1 ⟫
  unit⇔ : {m : ℕ} → ⟪ m ⟫ ⇔ ⟪ m +ℕ 0 ⟫

Better idea to explore:

The normal form is a list; most of the combinators shift the focus around;
the only real action is done by swap₊

Given

   x : ⟪ 6 ⟫
   x = (A + (B + (C + (D + (E + (F + O))))))

Want:

   x[2] to have type ⟪ 2 +ℕ 4 ⟫
   x[5] to have type ⟪ 5 +ℕ 1 ⟫
   etc

Perhaps use ideas from
https://gist.github.com/beala/d9e95c17999e1cd4f2d9b8bddff7768a#file-cryptol-agda-L43

-----------------------------------------------------------------------------
-- Example ctd

mirror : tree ⟷₁ eert
mirror = swap₊ ◎ (swap₊ ⊕ swap₊) ◎ ((id⟷₁ ⊕ swap₊) ⊕ (id⟷₁ ⊕ swap₊))

mirrorNF : canonU tree ⇔ canonU eert
mirrorNF = combNF mirror

Keeping A..F as postulates

seq⇔
  (bigSwap⇔ {∣ A ∣ +ℕ ∣ B ∣ +ℕ ∣ C ∣} {∣ D ∣ +ℕ ∣ E ∣ +ℕ ∣ F ∣})
  (seq⇔
    (append⇔
      (bigSwap⇔ {∣ D ∣ +ℕ ∣ E ∣} {∣ F ∣})
      (bigSwap⇔ {∣ A ∣ +ℕ ∣ B ∣} {∣ C ∣}))
    (append⇔
      (append⇔ id⇔
        (bigSwap⇔ {∣ D ∣} {∣ E ∣}))
      (append⇔ id⇔
        (bigSwap⇔ {∣ A ∣} {∣ B ∣}))))

A..F are all set to I

seq⇔
(seq⇔ snocN⇔
 (seq⇔ assocr⇔
  (seq⇔
   (seq⇔ snocN⇔
    (seq⇔ assocr⇔
     (seq⇔ (seq⇔ snocN⇔ (seq⇔ assocr⇔ (seq⇔ unit⇔ assocr⇔))) assocr⇔)))
   assocr⇔)))
(seq⇔
 (append⇔
  (seq⇔ snocN⇔
   (seq⇔ assocr⇔
    (seq⇔ (seq⇔ snocN⇔ (seq⇔ assocr⇔ (seq⇔ unit⇔ assocr⇔))) assocr⇔)))
  (seq⇔ snocN⇔
   (seq⇔ assocr⇔
    (seq⇔ (seq⇔ snocN⇔ (seq⇔ assocr⇔ (seq⇔ unit⇔ assocr⇔))) assocr⇔))))
 (append⇔
  (append⇔ id⇔ (seq⇔ snocN⇔ (seq⇔ assocr⇔ (seq⇔ unit⇔ assocr⇔))))
  (append⇔ id⇔ (seq⇔ snocN⇔ (seq⇔ assocr⇔ (seq⇔ unit⇔ assocr⇔))))))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
data _⇔_ : (t₁ t₂ : U) → Set where
  id⇔ : {m : ℕ} → ⟪ m ⟫ ⇔ ⟪ m ⟫
  seq⇔ : {m n k : ℕ} → ⟪ m ⟫ ⇔ ⟪ n ⟫ → ⟪ n ⟫ ⇔ ⟪ k ⟫ → ⟪ m ⟫ ⇔ ⟪ k ⟫
  append⇔ : {m n k p : ℕ} → ⟪ m ⟫ ⇔ ⟪ k ⟫ → ⟪ n ⟫ ⇔ ⟪ p ⟫ →
            ⟪ m +ℕ n ⟫ ⇔ ⟪ k +ℕ p ⟫
  assocl⇔ : {m n k : ℕ} → ⟪ m +ℕ (n +ℕ k) ⟫ ⇔ ⟪ (m +ℕ n)  +ℕ k ⟫
  assocr⇔ : {m n k : ℕ} → ⟪ (m +ℕ n) +ℕ k ⟫ ⇔ ⟪ m +ℕ (n +ℕ k) ⟫
  snocN⇔ : {m : ℕ} → ⟪ 1 +ℕ m ⟫ ⇔ ⟪ m +ℕ 1 ⟫
  unit⇔ : {m : ℕ} → ⟪ m ⟫ ⇔ ⟪ m +ℕ 0 ⟫
  -- moves the first element to the end via a sequence of 'm' swaps
  -- swap 0; swap 1; swap 2; ...; swap (m-1)

-----------------------------------------------------------------------------
-- Convert combinators to normal form

bigSwap⇔ : {m n : ℕ} → ⟪ m +ℕ n ⟫ ⇔ ⟪ n +ℕ m ⟫
bigSwap⇔ {O} {n} = unit⇔
bigSwap⇔ {S m} {n} =
  seq⇔ snocN⇔
  (seq⇔ (assocr⇔ {m} {n} {1})
  (seq⇔ (bigSwap⇔ {m} {n +ℕ 1})
  (assocr⇔ {n} {1} {m})))

combNF : {t₁ t₂ : U} → (c : t₁ ⟷₁ t₂) → (canonU t₁ ⇔ canonU t₂)
combNF unite₊l = id⇔
combNF uniti₊l = id⇔
combNF {t₁ + t₂} swap₊ = bigSwap⇔ {∣ t₁ ∣} {∣ t₂ ∣}
combNF {t₁ + (t₂ + t₃)} assocl₊ = assocl⇔ {∣ t₁ ∣}{∣ t₂ ∣}{∣ t₃ ∣}
combNF {(t₁ + t₂) + t₃} assocr₊ = assocr⇔ {∣ t₁ ∣}{∣ t₂ ∣}{∣ t₃ ∣}
combNF id⟷₁ = id⇔
combNF (c₁ ◎ c₂) = seq⇔ (combNF c₁) (combNF c₂)
combNF (c₁ ⊕ c₂) = append⇔ (combNF c₁) (combNF c₂)



OLD STUFF. KEEP FOR NOW
∣⟪⟫∣ : (n : ℕ) → ∣ ⟪ n ⟫ ∣ == n
∣⟪⟫∣ O = idp
∣⟪⟫∣ (S n) = ap S (∣⟪⟫∣ n)

canon-n : (m : ℕ) → canonU ⟪ m ⟫ == ⟪ m ⟫
canon-n O = idp
canon-n (S m) = ap (λ X → ⟪ S X ⟫) (∣⟪⟫∣ m)

canon-invol : (t : U) → canonU (canonU t) == canonU t
canon-invol t = ap ⟪_⟫ (∣⟪⟫∣ ∣ t ∣)

canonU-assoc : (t₁ t₂ t₃ : U) →
  canonU (t₁ + (t₂ + t₃)) == canonU ((t₁ + t₂) + t₃)
canonU-assoc t₁ t₂ t₃ rewrite +-assoc (∣ t₁ ∣) (∣ t₂ ∣) (∣ t₃ ∣) = idp

-----------------------------------------------------------------------------
-- Define special combinators for canonical forms
-- Want these to be sequences of assocs and swaps

snoc : (m : ℕ) → ⟪ 1 +ℕ m ⟫ ⟷₁ ⟪ m +ℕ 1 ⟫
snoc O = id⟷₁
snoc (S n) = swap01 ◎ (id⟷₁ ⊕ snoc n)

dneppa : (m n : ℕ) → ⟪ m +ℕ n ⟫ ⟷₁ ⟪ n +ℕ m ⟫
dneppa O n = {!!}
dneppa (S m) n =
  ⟪ S (m +ℕ n) ⟫
  ⟷₁⟨ snoc (m +ℕ n) ⟩
  ⟪ (m +ℕ n) +ℕ 1 ⟫
  ⟷₁⟨ {!!} ⟩
  ⟪ m +ℕ (n +ℕ 1) ⟫
  ⟷₁⟨ dneppa m (n +ℕ 1) ⟩
  ⟪ (n +ℕ 1) +ℕ m ⟫
  ⟷₁⟨ {!!} ⟩
  ⟪ n +ℕ S m ⟫ ⟷₁∎

combNormalForm : {t₁ t₂ : U} → (c : t₁ ⟷₁ t₂) →
  Σ (canonU t₁ ⟷₁ canonU t₂) (λ cnf → (!⟷₁ (normC t₁) ◎ c ◎ normC t₂) ⟷₂ cnf)
combNormalForm {t} id⟷₁ = id⟷₁ ,
  trans⟷₂ (id⟷₂ ⊡ idl◎l) rinv◎l
combNormalForm {O + t} unite₊l = id⟷₁ ,
  trans⟷₂ (uniti₊l⟷₂l ⊡ id⟷₂)
  (trans⟷₂ assoc◎r
  (trans⟷₂ (id⟷₂ ⊡ assoc◎l)
  (trans⟷₂ (id⟷₂ ⊡ (linv◎l ⊡ id⟷₂))
  (trans⟷₂ (id⟷₂ ⊡ idl◎l)
  rinv◎l))))
combNormalForm {t} uniti₊l = id⟷₁ ,
  trans⟷₂ (id⟷₂ ⊡ assoc◎l)
  (trans⟷₂ (id⟷₂ ⊡ (uniti₊l⟷₂l ⊡ id⟷₂))
  (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
  (trans⟷₂ (id⟷₂ ⊡ (id⟷₂ ⊡ linv◎l))
  (trans⟷₂ (id⟷₂ ⊡ idr◎l)
  rinv◎l))))
combNormalForm {t₁ + t₂} swap₊ = dneppa ∣ t₁ ∣ ∣ t₂ ∣ ,
  {!!}
combNormalForm {t₁ + (t₂ + t₃)} assocl₊ = {!!} ,
  {!!}
combNormalForm {(t₁ + t₂) + t₃} assocr₊ = {!!} ,
  {!!}
combNormalForm (_◎_ {t₁} {t₂} {t₃} c₁ c₂) =
  let (c1nf , p1) = combNormalForm c₁
      (c2nf , p2) = combNormalForm c₂
  in (c1nf ◎ c2nf) ,
     (trans⟷₂
     (id⟷₂ ⊡ (((trans⟷₂ idr◎r (id⟷₂ ⊡ linv◎r {c = c₂})) ⊡ id⟷₂) ⊡ id⟷₂))
     (trans⟷₂ (id⟷₂ ⊡ ((assoc◎l ⊡ id⟷₂) ⊡ id⟷₂))
     (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
     (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
     (trans⟷₂ assoc◎l
     {!!})))))
combNormalForm {t₁ + t₂} {t₃ + t₄} (c₁ ⊕ c₂) =
  let (c1nf , p1) = combNormalForm c₁
      (c2nf , p2) = combNormalForm c₂
  in (!⟷₁ ⟪++⟫ ◎ (c1nf ⊕ c2nf) ◎ ⟪++⟫) ,
  {!!}
combNormalForm swap01 = {!!} ,
  {!!}

-----------------------------------------------------------------------------
-- Example

A1 A2 A3 A4 A5 A6 : U
A1 = I
A2 = I
A3 = I
A4 = I
A5 = I
A6 = I

tree : U
tree = ((A1 + A2) + A3) + ((A4 + A5) + A6)

mirrorTree : U
mirrorTree = (A6 + (A5 + A4)) + (A3 + (A2 + A1))

mirror : tree ⟷₁ mirrorTree
mirror = swap₊ ◎ (swap₊ ⊕ swap₊) ◎ ((id⟷₁ ⊕ swap₊) ⊕ (id⟷₁ ⊕ swap₊))

mirrorNF : canonU tree ⟷₁ canonU mirrorTree
mirrorNF = fst (combNormalForm mirror)

-----------------------------------------------------------------------------

infix 100 _″

_″ : ∀ {t₁ t₂} → t₁ ⇔ t₂ → t₁ ⟷₁ t₂
(id⇔ eq) ″ = idupto⟷₁ {_} {_} {ap canonU eq}
seq⇔ c₁ c₂ ″ = c₁ ″ ◎ c₂ ″
bigplus⇔ c₁ c₂ ″ = !⟷₁ ⟪++⟫ ◎ (c₁ ″ ⊕ c₂ ″) ◎ ⟪++⟫
bigswap⇔ {t₁} {t₂} ″ = dneppa ∣ t₁ ∣ ∣ t₂ ∣

data _⇔_ : (t₁ t₂ : U) → Set where
  id⇔ : {t₁ t₂ : U} → (canonU t₁ == canonU t₂) → canonU t₁ ⇔ canonU t₂
  seq⇔ : {t₁ t₂ t₃ : U} → (canonU t₁ ⇔ canonU t₂) → (canonU t₂ ⇔ canonU t₃) →
         (canonU t₁ ⇔ canonU t₃)
  bigswap⇔ : {t₁ t₂ : U} → canonU (t₁ + t₂) ⇔ canonU (t₂ + t₁)
  -- say | t₁ ∣ = 2 with elements {A,B} and ∣ t₂ = 3 ∣ with elements {C,D,E}, then
  -- canonU (t₁ + t₂) = (A + (B + (C + (D + (E + 0)))))
  -- the result of bigswap should be:
  -- (C + (D + (E + (A + (B + 0)))))
  -- below we express bigswap using a sequence of swaps
  bigplus⇔ : {t₁ t₂ t₃ t₄ : U} →
             (canonU t₁ ⇔ canonU t₃) → (canonU t₂ ⇔ canonU t₄) →
             (canonU (t₁ + t₂) ⇔ canonU (t₃ + t₄))
  -- say | t₁ ∣ = 2 with elements {A,B} and ∣ t₂ = 3 ∣ with elements {C,D,E}, then
  -- say c₁ maps (A + (B + 0)) to (X + (Y + 0))
  -- and c₂ maps (C + (D + (E + 0))) to (V + (W + (Z + 0)))
  -- we have canonU (t₁ + t₂) = (A + (B + (C + (D + (E + 0)))))
  -- the result of bigplus should be:
  -- (X + (Y + (V + (W + (Z + 0)))))


<swap-big : (t₁ t₂ : U) → canonU (t₁ + t₂) ⟷₁ canonU (t₂ + t₁)
swap-big O t₂ = id⟷₁
swap-big I O = id⟷₁
swap-big I I = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
swap-big I (t₂ + t₃) =
  (id⟷₁ ⊕ !⟷₁ (⟪+⟫ ∣ t₂ ∣ ∣ t₃ ∣)) ◎
  assocl₊ ◎
  (swap-big I t₂ ⊕ id⟷₁) ◎
  (!⟷₁ (⟪+⟫ ∣ t₂ ∣ ∣ I ∣) ⊕ id⟷₁) ◎
  assocr₊ ◎
  {!!}
swap-big (t₁ + t₃) t₂ = {!!}

⟪+⟫-assoc : (m n k : ℕ) →
  (id⟷₁ ⊕ ⟪+⟫ n k) ◎ ⟪+⟫ m (n +ℕ k) ⟷₂
  assocl₊ ◎ (⟪+⟫ m n ⊕ id⟷₁) ◎ ⟪+⟫ (m +ℕ n) k
⟪+⟫-assoc O n k = trans⟷₂ unite₊l⟷₂r (trans⟷₂ (triangle⊕l ⊡ id⟷₂) assoc◎r)
⟪+⟫-assoc (S m) n k =
    ((id⟷₁ ⊕ ⟪+⟫ n k) ◎ assocr₊ ◎ (id⟷₁ ⊕ ⟪+⟫ m (n +ℕ k)))
  ⟷₂⟨ {!!} ⟩
    ((assocl₊ ◎ ((assocr₊ ◎ (id⟷₁ ⊕ ⟪+⟫ m n)) ⊕ id⟷₁)) ◎ (assocr₊ ◎ (id⟷₁ ⊕ ⟪+⟫ (m +ℕ n) k)))
  ⟷₂⟨ assoc◎r ⟩
    (assocl₊ ◎ (((assocr₊ ◎ (id⟷₁ ⊕ ⟪+⟫ m n)) ⊕ id⟷₁) ◎ (assocr₊ ◎ (id⟷₁ ⊕ ⟪+⟫ (m +ℕ n) k))))
  ⟷₂∎

combNormalForm : {t₁ t₂ : U} → (c : t₁ ⟷₁ t₂) →
  Σ (canonU t₁ ⟷₁ canonU t₂) (λ nc → (!⟷₁ (normC t₁) ◎ c ◎ (normC t₂) ⟷₂ nc))
combNormalForm id⟷₁ = id⟷₁ ,
  trans⟷₂ (id⟷₂ ⊡ idl◎l) rinv◎l
combNormalForm unite₊l = id⟷₁ ,
  trans⟷₂ (uniti₊l⟷₂l ⊡ id⟷₂)
  (trans⟷₂ assoc◎r
  (trans⟷₂ (id⟷₂ ⊡ assoc◎l)
  (trans⟷₂ (id⟷₂ ⊡ (linv◎l ⊡ id⟷₂))
  (trans⟷₂ (id⟷₂ ⊡ idl◎l)
  rinv◎l))))
combNormalForm uniti₊l = id⟷₁ ,
  trans⟷₂ (id⟷₂ ⊡ assoc◎l)
  (trans⟷₂ (id⟷₂ ⊡ (uniti₊l⟷₂l ⊡ id⟷₂))
  (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
  (trans⟷₂ (id⟷₂ ⊡ (id⟷₂ ⊡ linv◎l))
  (trans⟷₂ (id⟷₂ ⊡ idr◎l)
  rinv◎l))))
combNormalForm {t₁ + t₂} {t₂ + t₁} swap₊ = swap-big t₁ t₂ ,
  {!!}
combNormalForm {t₁ + (t₂ + t₃)} assocl₊ = id⟷₁ ,
  {!!}

 ! <+> |t1| |t2+t3| ;
 id + (! (<+> |t2| |t3|)) ;
 ! norm t1 + (! norm t2 + ! norm t3) ;
  assocl+ ;
 (norm t1 + norm t2) + norm t3 ;
 (<+> |t1| |t2|) + id ;
 <+> |t1+t2| |t3|

-- formally:
--   transport (λ X → canonU (t₁ + (t₂ + t₃)) ⟷₁ X)
--             (canonU-assoc t₁ t₂ t₃) id⟷₁ ,
--   {!!}
combNormalForm {(t₁ + t₂) + t₃} assocr₊ = id⟷₁ ,
  {!!}
combNormalForm (c₁ ◎ c₂) with combNormalForm c₁ | combNormalForm c₂
... | nc₁ , eq₁ | nc₂ , eq₂ = (nc₁ ◎ nc₂) ,
  {!!}
combNormalForm (c₁ ⊕ c₂) with combNormalForm c₁ | combNormalForm c₂
... | nc₁ , eq₁ | nc₂ , eq₂ = {!!} ,
  {!!}

     assocrNormalForm : {t₁ t₂ t₃ nt : U} {c : t₁ + (t₂ + t₃) ⟷₁ nt} →
                        (nf : normalForm (t₁ + (t₂ + t₃)) nt c) →
                    combNormalForm assocr₊ (sum+NF nf) nf id⟷₁
                      rinv◎l
     swap0NormalForm : {t nt : U} {c : t ⟷₁ nt} {nf : normalForm t nt c}
                       {nc : nt ⟷₁ nt}
                       {c=nc : (!⟷₁ (unite₊l ◎ c) ◎ swap₊ ◎ swap₊ ◎ unite₊l ◎ c) ⟷₂ nc} →
                    combNormalForm swap₊ (sum0NF nf) (swap0NF (sum0NF nf)) id⟷₁
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎l)
                      (trans⟷₂ (id⟷₂ ⊡ (rinv◎l ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ idl◎l)
                      rinv◎l)))
     swap10NormalForm :
       combNormalForm swap₊ (sum1NF zeroNF) (sum0NF oneNF) id⟷₁
         {!!}
     swap11NormalForm :
       combNormalForm swap₊ (sum1NF oneNF) (sum1NF oneNF) (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
         {!!}
     -- swap1+NormalForm :
     --
     -- I + (a + b)     --------      (a + b) + I
     --                               a + (b + I)
     -- I + a* + b* + 0            a* + b* + I + 0
     --
     -- swap+NormalForm : (t₁ + t₂) + t₃
       swap₊
       O + t
       I + t
       (t₁ + t₂) + t₃
       {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
       (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
       (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set
     seqNormalForm : {t₁ t₂ t₃ nt₁ nt₂ nt₃ : U}
                     {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} {c₃ : t₃ ⟷₁ nt₃} →
                     {c₁₂ : t₁ ⟷₁ t₂} {c₂₃ : t₂ ⟷₁ t₃}
                     {nf₁ : normalForm t₁ nt₁ c₁} {nf₂ : normalForm t₂ nt₂ c₂}
                     {nf₃ : normalForm t₃ nt₃ c₃}
                     {nc₁₂ : nt₁ ⟷₁ nt₂} {nc₂₃ : nt₂ ⟷₁ nt₃}
                     {c₁₂=nc₁₂ : (!⟷₁ c₁ ◎ c₁₂ ◎ c₂) ⟷₂ nc₁₂}
                     {c₂₃=nc₂₃ : (!⟷₁ c₂ ◎ c₂₃ ◎ c₃) ⟷₂ nc₂₃} →
                     combNormalForm c₁₂ nf₁ nf₂ nc₁₂ c₁₂=nc₁₂ →
                     combNormalForm c₂₃ nf₂ nf₃ nc₂₃ c₂₃=nc₂₃ →
                    combNormalForm (c₁₂ ◎ c₂₃) nf₁ nf₃ (nc₁₂ ◎ nc₂₃)
                      (trans⟷₂
                        (id⟷₂ ⊡
                          (((trans⟷₂ idr◎r (id⟷₂ ⊡ linv◎r {c = c₂})) ⊡ id⟷₂) ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ ((assoc◎l ⊡ id⟷₂) ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
                      (trans⟷₂ assoc◎l
                      (c₁₂=nc₁₂ ⊡ c₂₃=nc₂₃))))))
     -- sumNormalForm : (c₁ ⊕ c₂)
       {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
       (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
       (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set

-----------------------------------------------------------------------------

data normalForm : (t : U) → (nt : U) → (t ⟷₁ nt) → Set where
  zeroNF : normalForm O O id⟷₁
  oneNF  : normalForm I (I + O) (uniti₊l ◎ swap₊)
  sum0NF  : {t nt : U} {c : t ⟷₁ nt} →
           normalForm t nt c →
           normalForm (O + t) nt (unite₊l ◎ c)
  sum1NF  : {t nt : U} {c : t ⟷₁ nt} →
           normalForm t nt c →
           normalForm (I + t) (I + nt) (id⟷₁ ⊕ c)
  sum+NF  : {t₁ t₂ t₃ nt : U} {c : t₁ + (t₂ + t₃) ⟷₁ nt} →
           normalForm (t₁ + (t₂ + t₃)) nt c →
           normalForm ((t₁ + t₂) + t₃) nt (assocr₊ ◎ c)
  swap0NF : {t nt : U} {c : O + t ⟷₁ nt} →
           normalForm (O + t) nt c →
           normalForm (t + O) nt (swap₊ ◎ c)

{-# TERMINATING #-} -- fix later
normalize : (t : U) → Σ U (λ nt → Σ (t ⟷₁ nt) (λ c → normalForm t nt c))
normalize O = O , _ , zeroNF
normalize I = (I + O) , _ , oneNF
normalize (O + t) with normalize t
... | nt , nc , nf = _ , _ , sum0NF nf
normalize (I + t) with normalize t
... | nt , nc , nf = _ , _ , sum1NF nf
normalize ((t₁ + t₂) + t₃) with normalize (t₁ + (t₂ + t₃))
... | nt , nc , nf = _ , _ , sum+NF nf

-- Example of taking a combinator between regular types and producing one
-- between normal forms along with a proof of 2-equivalence

-- For readability
-- Regular Pi combinator on trees


A1 A2 A3 A4 A5 A6 : U
A1 = I
A2 = I
A3 = I
A4 = I
A5 = I
A6 = I

tree : U
tree = ((A1 + A2) + A3) + ((A4 + A5) + A6)

mirrorTree : U
mirrorTree = (A6 + (A5 + A4)) + (A3 + (A2 + A1))

mirror : tree ⟷₁ mirrorTree
mirror = swap₊ ◎ (swap₊ ⊕ swap₊) ◎ ((id⟷₁ ⊕ swap₊) ⊕ (id⟷₁ ⊕ swap₊))

-- Flattened normal-form types

flatTree : U
flatTree = A1 + (A2 + (A3 + (A4 + (A5 + (A6 + O)))))

flatMirrorTree : U
flatMirrorTree = A6 + (A5 + (A4 + (A3 + (A2 + (A1 + O)))))

-- Going from regular Pi types to the normal form

treeNF : Σ (tree ⟷₁ flatTree) (λ c → normalForm tree flatTree c)
treeNF = _ , sum+NF (sum+NF (sum1NF (sum1NF (sum1NF (sum+NF (sum1NF (sum1NF oneNF)))))))

Evaluating treeNF produces
(assocr₊ ◎
 assocr₊ ◎
 id⟷₁ ⊕
 id⟷₁ ⊕ id⟷₁ ⊕ assocr₊ ◎ id⟷₁ ⊕ id⟷₁ ⊕ (uniti₊l ◎ swap₊))

mirrorTreeNF : Σ (mirrorTree ⟷₁ flatMirrorTree) (λ c → normalForm mirrorTree flatMirrorTree c)
mirrorTreeNF = _ , sum+NF (sum1NF (sum+NF (sum1NF (sum1NF (sum1NF (sum1NF oneNF))))))

Evaluating mirrorTreeNF produces
(assocr₊ ◎
 id⟷₁ ⊕
 assocr₊ ◎ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ (uniti₊l ◎ swap₊))

-- Now we want to define a normal form for combinators and relate 'mirror' to its
-- normal form

-- Pay attention to nc below: allowed normal form combinators:
-- nc ::= id⟷₁
--     | !⟷₁ nc
--     | nc ◎ nc
--

data comb+NormalForm : {t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
                    (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
                    (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set where


data combNormalForm : {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
                    (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
                    (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set where
     idNormalForm : {t nt : U} {c : t ⟷₁ nt} → (nf : normalForm t nt c) →
                    combNormalForm id⟷₁ nf nf id⟷₁
                      (trans⟷₂ (id⟷₂ ⊡ idl◎l) rinv◎l)
     uniteNormalForm : {t nt : U} {c : t ⟷₁ nt} → (nf : normalForm t nt c) →
                    combNormalForm unite₊l (sum0NF nf) nf id⟷₁
                      rinv◎l
     unitiNormalForm : {t nt : U} {c : t ⟷₁ nt} → (nf : normalForm t nt c) →
                    combNormalForm uniti₊l nf (sum0NF nf) id⟷₁
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎l)
                      (trans⟷₂ (id⟷₂ ⊡ (linv◎l ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ idl◎l)
                      rinv◎l)))
     assoclNormalForm : {t₁ t₂ t₃ nt : U} {c : t₁ + (t₂ + t₃) ⟷₁ nt} →
                        (nf : normalForm (t₁ + (t₂ + t₃)) nt c) →
                    combNormalForm assocl₊ nf (sum+NF nf) id⟷₁
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎l)
                      (trans⟷₂ (id⟷₂ ⊡ (linv◎l ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ idl◎l) rinv◎l)))
     assocrNormalForm : {t₁ t₂ t₃ nt : U} {c : t₁ + (t₂ + t₃) ⟷₁ nt} →
                        (nf : normalForm (t₁ + (t₂ + t₃)) nt c) →
                    combNormalForm assocr₊ (sum+NF nf) nf id⟷₁
                      rinv◎l
     swap0NormalForm : {t nt : U} {c : t ⟷₁ nt} {nf : normalForm t nt c}
                       {nc : nt ⟷₁ nt}
                       {c=nc : (!⟷₁ (unite₊l ◎ c) ◎ swap₊ ◎ swap₊ ◎ unite₊l ◎ c) ⟷₂ nc} →
                    combNormalForm swap₊ (sum0NF nf) (swap0NF (sum0NF nf)) id⟷₁
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎l)
                      (trans⟷₂ (id⟷₂ ⊡ (rinv◎l ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ idl◎l)
                      rinv◎l)))
     swap10NormalForm :
       combNormalForm swap₊ (sum1NF zeroNF) (sum0NF oneNF) id⟷₁
         {!!}
     swap11NormalForm :
       combNormalForm swap₊ (sum1NF oneNF) (sum1NF oneNF) (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
         {!!}
     -- swap1+NormalForm :
     --
     -- I + (a + b)     --------      (a + b) + I
     --                               a + (b + I)
     -- I + a* + b* + 0            a* + b* + I + 0
     --
     -- swap+NormalForm : (t₁ + t₂) + t₃
       swap₊
       O + t
       I + t
       (t₁ + t₂) + t₃
       {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
       (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
       (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set
     seqNormalForm : {t₁ t₂ t₃ nt₁ nt₂ nt₃ : U}
                     {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} {c₃ : t₃ ⟷₁ nt₃} →
                     {c₁₂ : t₁ ⟷₁ t₂} {c₂₃ : t₂ ⟷₁ t₃}
                     {nf₁ : normalForm t₁ nt₁ c₁} {nf₂ : normalForm t₂ nt₂ c₂}
                     {nf₃ : normalForm t₃ nt₃ c₃}
                     {nc₁₂ : nt₁ ⟷₁ nt₂} {nc₂₃ : nt₂ ⟷₁ nt₃}
                     {c₁₂=nc₁₂ : (!⟷₁ c₁ ◎ c₁₂ ◎ c₂) ⟷₂ nc₁₂}
                     {c₂₃=nc₂₃ : (!⟷₁ c₂ ◎ c₂₃ ◎ c₃) ⟷₂ nc₂₃} →
                     combNormalForm c₁₂ nf₁ nf₂ nc₁₂ c₁₂=nc₁₂ →
                     combNormalForm c₂₃ nf₂ nf₃ nc₂₃ c₂₃=nc₂₃ →
                    combNormalForm (c₁₂ ◎ c₂₃) nf₁ nf₃ (nc₁₂ ◎ nc₂₃)
                      (trans⟷₂
                        (id⟷₂ ⊡
                          (((trans⟷₂ idr◎r (id⟷₂ ⊡ linv◎r {c = c₂})) ⊡ id⟷₂) ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ ((assoc◎l ⊡ id⟷₂) ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
                      (trans⟷₂ assoc◎l
                      (c₁₂=nc₁₂ ⊡ c₂₃=nc₂₃))))))
     -- sumNormalForm : (c₁ ⊕ c₂)
       {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
       (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
       (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set


mirrorNF : Σ (flatTree ⟷₁ flatMirrorTree) (λ nc →
           Σ (!⟷₁ (fst treeNF) ◎ mirror ◎ fst mirrorTreeNF ⟷₂ nc) (λ α →
           combNormalForm mirror (snd treeNF) (snd mirrorTreeNF) nc α))
mirrorNF = _ , _ ,
  seqNormalForm {!!}
  (seqNormalForm {!!}
  {!!})
--}
