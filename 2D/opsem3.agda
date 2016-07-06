{-# OPTIONS --without-K #-}

module 2D.opsem3 where

open import Data.Sum hiding ([_,_])
open import Data.Product hiding (<_,_>;,_) renaming (_,_ to _&_ )

open import Data.Unit using (⊤; tt)
open import Data.Fin as F hiding (#_;_<_)
open import Data.Nat using (ℕ; suc; _≥_) renaming (_+_ to _ℕ+_)
open import Data.Integer
  using (ℤ; +_; -[1+_])
  renaming (-_ to ℤ-; suc to ℤsuc; _+_ to _ℤ+_)
open import Rational+ renaming (_+_ to _ℚ+_; _*_ to _ℚ*_)
  hiding (_≤_; _≤?_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; subst; cong; sym; cong₂; inspect; [_])
open import Function using (case_of_)

open import 2D.Types
-- open import 2D.Order
open import 2D.Iter
open import 2D.Sing
open import 2D.SingIter
open import 2D.Power
open import 2D.Val
open import 2D.Prim
open import 2D.Order2Lemmas

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- Evaluation


Fin2⇒1+1 : Fin 2 → Val (𝟙 ⊕ 𝟙)
Fin2⇒1+1 zero = inl ⋆
Fin2⇒1+1 (suc zero) = inr ⋆
Fin2⇒1+1 (suc (suc ()))

mutual
  𝓐𝓹 : {T₁ T₂ : U} → (T₁ ⟷ T₂) → Val T₁ → Val T₂
  𝓐𝓹 (Prim x) v = prim x v
  𝓐𝓹 (c ◎ c₁) v =
    let x = 𝓐𝓹 c v in 𝓐𝓹 c₁ x
  𝓐𝓹 (c ⊕ c₁) (inl v) = inl (𝓐𝓹 c v)
  𝓐𝓹 (c ⊕ c₁) (inr v) = inr (𝓐𝓹 c₁ v)
  𝓐𝓹 (c ⊗ c₁) [ v , w ] = [ 𝓐𝓹 c v , 𝓐𝓹 c₁ w ]
  -- 𝓐𝓹 ap⟷ [ comb < i , q , α > , v₁ ] = [ (comb < i , q , α >) , (𝓐𝓹 q v₁) ]
  -- 𝓐𝓹 ap⁻¹⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹⁻¹ (Iter.q x) v₁) ]
  𝓐𝓹 (η- c) ⋆ = tangl (λ { q → q & id⇔ })
  𝓐𝓹 (η+ c) ⋆ = tangr ((λ { q → q & id⇔ }))
  𝓐𝓹 (ε+ c) p = ⋆
  𝓐𝓹 (ε- c) p = ⋆
  𝓐𝓹 synchr⋆ [ tangr x , v ] = [ v , tangl x ]
  𝓐𝓹 synchl⋆ [ v , tangl x ] = [ (tangr x) , v ]
  𝓐𝓹 (app-num\\ {t} {p} {q} {r} f) (tangl x) =
    -- q₁ is an Iter q.  f : # p ⟷ # r.
    tangl (λ { < j , q₁ , α > →
      let res = x (< j , q₁ , α >) in
      let vp = proj₁ res in -- itp is a Val (# p)
      let vr = 𝓐𝓹 f (comb vp) in -- Val (# r)
      let itr = get-iter vr in -- Iter r
      let pf = proj₂ res in
      let lift-f = lift# f in
      case itr of λ { ( < i , fx , β > ) → 
      itr & {!cong≈ f (#p≈ ? ? ?)!} } }) -- need an Iter r and a proof it's the same as q₁
  𝓐𝓹 (app-num// f) v = {!!}

  𝓐𝓹⁻¹ : {T₁ T₂ : U} → (T₁ ⟷ T₂) → Val T₂ → Val T₁
  𝓐𝓹⁻¹ (Prim x) v = prim⁻¹ x v
  𝓐𝓹⁻¹ (c ◎ c₁) v = 𝓐𝓹⁻¹ c (𝓐𝓹⁻¹ c₁ v)
  𝓐𝓹⁻¹ (c ⊕ c₁) (inl v) = inl (𝓐𝓹⁻¹ c v)
  𝓐𝓹⁻¹ (c ⊕ c₁) (inr v) = inr (𝓐𝓹⁻¹ c₁ v)
  𝓐𝓹⁻¹ (c ⊗ c₁) [ v , w ] = [ (𝓐𝓹⁻¹ c v) , (𝓐𝓹⁻¹ c₁ w) ]
  -- 𝓐𝓹⁻¹ ap⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹⁻¹ (Iter.q x) v₁) ]
  -- 𝓐𝓹⁻¹ ap⁻¹⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹 (Iter.q x) v₁) ]
  𝓐𝓹⁻¹ (η- c) p = ⋆ -- [ 1/comb x , comb < k , q , α > ] = 𝟙ₚ (si k α)
  𝓐𝓹⁻¹ (η+ c) p = ⋆ -- [ comb < k , q , α > , v₁ ] = 𝟙ₚ (si k α)
  𝓐𝓹⁻¹ (ε+ c) ⋆ = tangr ((λ { q → q & id⇔ })) -- [ (comb < k , c ^ k , id⇔ >) , (1/comb ⟪ c , id⇔ ⟫) ]
  𝓐𝓹⁻¹ (ε- c) ⋆ = tangl ((λ { q → q & id⇔ })) -- [ (1/comb ⟪ c , id⇔ ⟫) , (comb < k , (c ^ k) , id⇔ >) ]
  𝓐𝓹⁻¹ synchr⋆ [ v , tangl x ] = [ tangr x , v ]
  𝓐𝓹⁻¹ synchl⋆ [ tangr x , v₁ ] = [ v₁ , tangl x ]
  𝓐𝓹⁻¹ (app-num\\ f) v = {!!}
  𝓐𝓹⁻¹ (app-num// f) v = {!!}

  cong≈ : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) {v w : Val T₁} → v ≈ w → 𝓐𝓹 c v ≈ 𝓐𝓹 c w
  cong≈ (Prim x) {v} {w} p = prim-cong≈ x v w p -- prim-cong≈ x p
  cong≈ (c₁ ◎ c₂) p = cong≈ c₂ (cong≈ c₁ p)
  cong≈ (c₁ ⊕ c₂) {inl v} {inl w} (inj≈ p) = inj≈ (cong≈ c₁ p)
  cong≈ (c₁ ⊕ c₂) {inl v} {inr w} (inj≈ ())
  cong≈ (c₁ ⊕ c₂) {inr v} {inl w} (inj≈ ())
  cong≈ (c₁ ⊕ c₂) {inr v} {inr w} (inj≈ p) = inj≈ (cong≈ c₂ p)
  cong≈ (c₁ ⊗ c₂) {[ v , v₁ ]} {[ w , w₁ ]} ([,]≈ p₁ p₂) = [,]≈ (cong≈ c₁ p₁) (cong≈ c₂ p₂)
  -- cong≈ ap⟷ ([,]≈ (#p≈ {_} {p} (comb x) (comb x₁) x₂) p₂) =
  --   [,]≈ (#p≈ (comb x) (comb x₁) x₂) ({!!})
  -- cong≈ ap⁻¹⟷ ([,]≈ p₁ p₂) = {!!}
  cong≈ (η- c) {⋆} {⋆} ⋆≈ = tangl≈
  cong≈ (η+ c) ⋆≈ = tangr≈
  cong≈ (ε+ c) tangr≈ = ⋆≈
  cong≈ (ε- p) tangl≈ = ⋆≈
  cong≈ synchl⋆ {[ .(comb x₂) , tangl x ]} {[ .(comb x₃) , tangl x₁ ]} ([,]≈ (#p≈ (comb x₂) (comb x₃) x₄) tangl≈) = [,]≈ tangr≈ (#p≈ (comb x₂) (comb x₃) x₄)
  cong≈ synchr⋆ {[ tangr p , comb c ]} {[ tangr q , comb d ]} ([,]≈ tangr≈ (#p≈ _ _ x)) = [,]≈ (#p≈ (comb c) (comb d) x) tangl≈
  cong≈ (app-num// f) v = {!!}
  cong≈ (app-num\\ f) v = {!!}
  
cong⁻¹≈ : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → {v w : Val T₂} → v ≈ w → 𝓐𝓹⁻¹ c v ≈ 𝓐𝓹⁻¹ c w
cong⁻¹≈ (Prim x) {v} {w} p = prim⁻¹-cong≈ x v w p
cong⁻¹≈ (c₁ ◎ c₂) p = cong⁻¹≈ c₁ (cong⁻¹≈ c₂ p)
cong⁻¹≈ (c₁ ⊕ c₂) {inl v} {inl w} (inj≈ p) = inj≈ (cong⁻¹≈ c₁ p)
cong⁻¹≈ (c₁ ⊕ c₂) {inl v} {inr w} (inj≈ ())
cong⁻¹≈ (c₁ ⊕ c₂) {inr v} {inl w} (inj≈ ())
cong⁻¹≈ (c₁ ⊕ c₂) {inr v} {inr w} (inj≈ p) = inj≈ (cong⁻¹≈ c₂ p)
cong⁻¹≈ (c₁ ⊗ c₂) {[ v , v₁ ]} {[ w , w₁ ]} ([,]≈ p₁ p₂) = [,]≈ (cong⁻¹≈ c₁ p₁) (cong⁻¹≈ c₂ p₂)
-- cong⁻¹≈ ap⟷ ([,]≈ p₁ p₂) = {!!}
-- cong⁻¹≈ ap⁻¹⟷ ([,]≈ p₁ p₂) = {!!}
cong⁻¹≈ (η- p) eq = ⋆≈
cong⁻¹≈ (η+ p) eq = ⋆≈
cong⁻¹≈ (ε+ c) {⋆} {⋆} eq = tangr≈
cong⁻¹≈ (ε- c) {⋆} {⋆} eq = tangl≈
cong⁻¹≈ synchr⋆ {[ .x₂ , tangl x ]} {[ .w , tangl x₁ ]} ([,]≈ (#p≈ x₂ w x₃) tangl≈) = [,]≈ tangr≈ (#p≈ x₂ w x₃)
cong⁻¹≈ synchl⋆ {[ tangr x , v₁ ]} {[ tangr x₁ , w₁ ]} ([,]≈ eq eq₁) = [,]≈ eq₁ tangl≈
cong⁻¹≈ (app-num// f) v = {!!}
cong⁻¹≈ (app-num\\ f) v = {!!}

mutual
  fwd◎bwd≈id : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : Val T₂) → (𝓐𝓹 c (𝓐𝓹⁻¹ c v)) ≈ v
  fwd◎bwd≈id (Prim x) v = refl≈ (prim◎prim⁻¹≡id x v)
  fwd◎bwd≈id (c ◎ c₁) v = trans≈ (cong≈ c₁ (fwd◎bwd≈id c (𝓐𝓹⁻¹ c₁ v))) (fwd◎bwd≈id c₁ v)
  fwd◎bwd≈id (c ⊕ c₁) (inl v) = inj≈ (fwd◎bwd≈id c v)
  fwd◎bwd≈id (c ⊕ c₁) (inr v) = inj≈ (fwd◎bwd≈id c₁ v)
  fwd◎bwd≈id (c ⊗ c₁) [ v , v₁ ] = [,]≈ (fwd◎bwd≈id c v) (fwd◎bwd≈id c₁ v₁)
--   fwd◎bwd≈id ap⟷ [ comb {t} {p} < i , q , α > , v₁ ] =
--     [,]≈ (#p≈ (comb < i , q , α >) (comb < i , q , α >) linv◎l)
--          (fwd◎bwd≈id q v₁)
--   fwd◎bwd≈id ap⁻¹⟷ [ comb x , v₁ ] = [,]≈ (refl≈ refl) (bwd◎fwd≈id (Iter.q x) v₁)
  fwd◎bwd≈id (η- c) (tangl x) = tangl≈
  fwd◎bwd≈id (η+ c) (tangr x) = tangr≈
  fwd◎bwd≈id (ε+ c) ⋆ = ⋆≈
  fwd◎bwd≈id (ε- c) ⋆ = ⋆≈
  fwd◎bwd≈id synchl⋆ [ tangr x , v₁ ] = refl≈ refl
  fwd◎bwd≈id synchr⋆ [ v , tangl x ] = refl≈ refl
  fwd◎bwd≈id (app-num// f) v = {!!}
  fwd◎bwd≈id (app-num\\ f) v = {!!}

  bwd◎fwd≈id : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : Val T₁) → (𝓐𝓹⁻¹ c (𝓐𝓹 c v)) ≈ v
  bwd◎fwd≈id (Prim x) v = refl≈ (prim⁻¹◎prim≡id x v)
  bwd◎fwd≈id (c ◎ c₁) v = trans≈ (cong⁻¹≈ c (bwd◎fwd≈id c₁ (𝓐𝓹 c v))) (bwd◎fwd≈id c v)
  bwd◎fwd≈id (c ⊕ c₁) (inl v) = inj≈ (bwd◎fwd≈id c v)
  bwd◎fwd≈id (c ⊕ c₁) (inr v) = inj≈ (bwd◎fwd≈id c₁ v)
  bwd◎fwd≈id (c ⊗ c₁) [ v , v₁ ] = [,]≈ (bwd◎fwd≈id c v) (bwd◎fwd≈id c₁ v₁)
--   bwd◎fwd≈id ap⟷ [ comb x , v₁ ] = [,]≈ (refl≈ refl) (bwd◎fwd≈id (Iter.q x) v₁)
--   bwd◎fwd≈id ap⁻¹⟷ [ comb {t} {p} < i , q , α > , v₁ ] =
--     [,]≈ (#p≈ (comb < i , q , α >) (comb < i , q , α >) linv◎l)
--          (fwd◎bwd≈id q v₁)
  bwd◎fwd≈id (η- c) ⋆ = ⋆≈
  bwd◎fwd≈id (η+ c) ⋆ = ⋆≈
  bwd◎fwd≈id (ε+ c) (tangr x) = tangr≈
  bwd◎fwd≈id (ε- c) (tangl x) = tangl≈
  bwd◎fwd≈id synchl⋆ [ v , tangl x ] = refl≈ refl
  bwd◎fwd≈id synchr⋆ [ tangr x , v₁ ] = refl≈ refl
  bwd◎fwd≈id (app-num// f) v = {!!}
  bwd◎fwd≈id (app-num\\ f) v = {!!}

bwd-coherence : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : Val T₂) → 𝓐𝓹⁻¹ c v ≈ 𝓐𝓹 (! c) v
bwd-coherence (Prim unite₊l) v = inj≈ (refl≈ refl)
bwd-coherence (Prim uniti₊l) (inl ())
bwd-coherence (Prim uniti₊l) (inr v) = refl≈ refl
bwd-coherence (Prim unite₊r) v = inj≈ (refl≈ refl)
bwd-coherence (Prim uniti₊r) (inl v) = refl≈ refl
bwd-coherence (Prim uniti₊r) (inr ())
bwd-coherence (Prim swap₊) (inl v) = refl≈ refl
bwd-coherence (Prim swap₊) (inr v) = refl≈ refl
bwd-coherence (Prim assocl₊) (inl (inl v)) = refl≈ refl
bwd-coherence (Prim assocl₊) (inl (inr v)) = refl≈ refl
bwd-coherence (Prim assocl₊) (inr v) = inj≈ (refl≈ refl)
bwd-coherence (Prim assocr₊) (inl v) = inj≈ (refl≈ refl)
bwd-coherence (Prim assocr₊) (inr (inl v)) = inj≈ (refl≈ refl)
bwd-coherence (Prim assocr₊) (inr (inr v)) = inj≈ (refl≈ refl)
bwd-coherence (Prim unite⋆l) v = [,]≈ ⋆≈ (refl≈ refl)
bwd-coherence (Prim uniti⋆l) [ v , v₁ ] = refl≈ refl
bwd-coherence (Prim unite⋆r) v = [,]≈ (refl≈ refl) ⋆≈
bwd-coherence (Prim uniti⋆r) [ v , v₁ ] = refl≈ refl
bwd-coherence (Prim swap⋆) [ v , v₁ ] = [,]≈ (refl≈ refl) (refl≈ refl)
bwd-coherence (Prim assocl⋆) [ [ v , v₁ ] , v₂ ] = [,]≈ (refl≈ refl) (refl≈ refl)
bwd-coherence (Prim assocr⋆) [ v , [ v₁ , v₂ ] ] = [,]≈ (refl≈ refl) (refl≈ refl)
bwd-coherence (Prim absorbr) ()
bwd-coherence (Prim absorbl) ()
bwd-coherence (Prim factorzr) [ v , v₁ ] = refl≈ refl
bwd-coherence (Prim factorzl) [ v , v₁ ] = refl≈ refl
bwd-coherence (Prim dist) (inl [ v , v₁ ]) = [,]≈ (refl≈ refl) (refl≈ refl)
bwd-coherence (Prim dist) (inr [ v , v₁ ]) = [,]≈ (refl≈ refl) (refl≈ refl)
bwd-coherence (Prim factor) [ inl v , v₁ ] = inj≈ (refl≈ refl)
bwd-coherence (Prim factor) [ inr v , v₁ ] = inj≈ (refl≈ refl)
bwd-coherence (Prim distl) (inl [ v , v₁ ]) = [,]≈ (refl≈ refl) (refl≈ refl)
bwd-coherence (Prim distl) (inr [ v , v₁ ]) = [,]≈ (refl≈ refl) (refl≈ refl)
bwd-coherence (Prim factorl) [ v , inl v₁ ] = inj≈ (refl≈ refl)
bwd-coherence (Prim factorl) [ v , inr v₁ ] = inj≈ (refl≈ refl)
bwd-coherence (Prim id⟷) v = refl≈ refl
bwd-coherence (c ◎ c₁) v = 
  let eq = bwd-coherence c₁ v in
  trans≈ (cong⁻¹≈ c eq) (bwd-coherence c (𝓐𝓹 (! c₁) v))
bwd-coherence (c ⊕ c₁) (inl v) = inj≈ (bwd-coherence c v)
bwd-coherence (c ⊕ c₁) (inr v) = inj≈ (bwd-coherence c₁ v)
bwd-coherence (c ⊗ c₁) [ v , v₁ ] = [,]≈ (bwd-coherence c v) (bwd-coherence c₁ v₁)
bwd-coherence (η- c) v = ⋆≈
bwd-coherence (η+ c) v = ⋆≈
bwd-coherence (ε+ c) ⋆ = tangr≈
bwd-coherence (ε- c) ⋆ = tangl≈
bwd-coherence synchl⋆ [ tangr x , v₁ ] = refl≈ refl
bwd-coherence synchr⋆ [ v , tangl x ] = refl≈ refl
bwd-coherence (app-num// f) v = {!!}
bwd-coherence (app-num\\ f) v = {!!}

lemma-1 : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : Val T₁) → 𝓐𝓹 (! c) (𝓐𝓹 c v) ≈ v
lemma-1 c v = trans≈ (sym≈ (bwd-coherence c (𝓐𝓹 c v))) (bwd◎fwd≈id c v)

lemma-2 : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : Val T₂) → 𝓐𝓹 c (𝓐𝓹 (! c) v) ≈ v
lemma-2 c v = trans≈ (cong≈ c (sym≈ (bwd-coherence c v))) (fwd◎bwd≈id c v)

lemma-3 : {T₁ T₂ T₃ : U} → (c₁ : T₁ ⟷ T₂) (c₂ : T₂ ⟷ T₃) → (v : Val T₁) → 𝓐𝓹 (c₁ ◎ c₂) v ≈ 𝓐𝓹 c₂ (𝓐𝓹 c₁ v)
lemma-3 c₁ c₂ ⋆ = refl≈ refl
lemma-3 c₁ c₂ (inl v) = refl≈ refl
lemma-3 c₁ c₂ (inr v) = refl≈ refl
lemma-3 c₁ c₂ [ v₁ , v₂ ] = refl≈ refl
lemma-3 c₁ c₂ (comb x) = refl≈ refl
lemma-3 c₁ c₂ (tangr x) = refl≈ refl
lemma-3 c₁ c₂ (tangl x) = refl≈ refl

lemma-4 : {T : U} → (v : Val T) → 𝓐𝓹 (Prim id⟷) v ≈ v
lemma-4 v = refl≈ refl

lemma-5 : {T₁ T₂ T₃ : U} → (c₁ : T₁ ⟷ T₂) (c₂ : T₂ ⟷ T₃) → (v : Val T₃) → 𝓐𝓹⁻¹ (c₁ ◎ c₂) v ≈ 𝓐𝓹⁻¹ c₁ (𝓐𝓹⁻¹ c₂ v)
lemma-5 c₁ c₂ ⋆ = refl≈ refl
lemma-5 c₁ c₂ (inl v) = refl≈ refl
lemma-5 c₁ c₂ (inr v) = refl≈ refl
lemma-5 c₁ c₂ [ v , v₁ ] = refl≈ refl
lemma-5 c₁ c₂ (comb x) = refl≈ refl
lemma-5 c₁ c₂ (tangr x) = refl≈ refl
lemma-5 c₁ c₂ (tangl x) = refl≈ refl

-- most cases are symmetric, could be made more concise
fwd-2-coherence : {T₁ T₂ : U} → (c₁ c₂ : T₁ ⟷ T₂) → (p : c₁ ⇔ c₂) → (v : Val T₁) → 𝓐𝓹 c₁ v ≈ 𝓐𝓹 c₂ v
fwd-2-coherence _ _ assoc◎l v = refl≈ refl
fwd-2-coherence _ _ assoc◎r v = refl≈ refl
fwd-2-coherence .(Prim id⟷ ◎ c₂) c₂ idl◎l v = refl≈ refl
fwd-2-coherence c₁ .(Prim id⟷ ◎ c₁) idl◎r v = refl≈ refl
fwd-2-coherence .(c₂ ◎ Prim id⟷) c₂ idr◎l v = refl≈ refl
fwd-2-coherence c₁ .(c₁ ◎ Prim id⟷) idr◎r v = refl≈ refl
fwd-2-coherence c₁ .c₁ id⇔ v = refl≈ refl
fwd-2-coherence .(! (Prim x) ◎ Prim x) .(Prim id⟷) (rinv◎l {c = Prim x}) v = lemma-2 (Prim x) v
fwd-2-coherence .((! c₁ ◎ ! c) ◎ c ◎ c₁) .(Prim id⟷) (rinv◎l {c = c ◎ c₁}) v = lemma-2 (c ◎ c₁) v
fwd-2-coherence .((! c ⊕ ! c₁) ◎ (c ⊕ c₁)) .(Prim id⟷) (rinv◎l {c = c ⊕ c₁}) v = lemma-2 (c ⊕ c₁) v
fwd-2-coherence .(! c ⊗ ! c₁ ◎ c ⊗ c₁) .(Prim id⟷) (rinv◎l {c = c ⊗ c₁}) v = lemma-2 (c ⊗ c₁) v
fwd-2-coherence .(ε- c ◎ η- c) .(Prim id⟷) (rinv◎l {c = η- c}) v = lemma-2 (ε- c ◎ η- c) v
fwd-2-coherence .(ε+ c ◎ η+ c) .(Prim id⟷) (rinv◎l {c = η+ c}) v = lemma-2 (ε+ c ◎ η+ c) v
fwd-2-coherence .(η+ c ◎ ε+ c) .(Prim id⟷) (rinv◎l {c = ε+ c}) v = lemma-2 (η+ c ◎ ε+ c) v
fwd-2-coherence .(η- c ◎ ε- c) .(Prim id⟷) (rinv◎l {c = ε- c}) v = lemma-2 (η- c ◎ ε- c) v
fwd-2-coherence .(synchl⋆ ◎ synchr⋆) .(Prim id⟷) (rinv◎l {c = synchr⋆}) v = lemma-2 synchr⋆ v
fwd-2-coherence .(synchr⋆ ◎ synchl⋆) .(Prim id⟷) (rinv◎l {c = synchl⋆}) v = lemma-2 synchl⋆ v
fwd-2-coherence .(app-num\\ (! c₃) ◎ app-num\\ c₃) .(Prim id⟷) (rinv◎l {c = app-num\\ c₃}) v = lemma-2 (app-num\\ c₃) v
fwd-2-coherence .(app-num// (! c₃) ◎ app-num// c₃) .(Prim id⟷) (rinv◎l {c = app-num// c₃}) v = lemma-2 (app-num// c₃) v
fwd-2-coherence .(Prim id⟷) .(! (Prim x) ◎ Prim x) (rinv◎r {c = Prim x}) v = sym≈ (lemma-2 (Prim x) v)
fwd-2-coherence .(Prim id⟷) .((! c₁ ◎ ! c) ◎ c ◎ c₁) (rinv◎r {c = c ◎ c₁}) v = sym≈ (lemma-2 (c ◎ c₁) v)
fwd-2-coherence .(Prim id⟷) .((! c ⊕ ! c₁) ◎ (c ⊕ c₁)) (rinv◎r {c = c ⊕ c₁}) v = sym≈ (lemma-2 (c ⊕ c₁) v)
fwd-2-coherence .(Prim id⟷) .(! c ⊗ ! c₁ ◎ c ⊗ c₁) (rinv◎r {c = c ⊗ c₁}) v = sym≈ (lemma-2 (c ⊗ c₁) v)
fwd-2-coherence .(Prim id⟷) .(ε- c ◎ η- c) (rinv◎r {c = η- c}) v = sym≈ (lemma-2 (ε- c ◎ η- c) v)
fwd-2-coherence .(Prim id⟷) .(ε+ c ◎ η+ c) (rinv◎r {c = η+ c}) v = sym≈ (lemma-2 (ε+ c ◎ η+ c) v)
fwd-2-coherence .(Prim id⟷) .(η+ c ◎ ε+ c) (rinv◎r {c = ε+ c}) v = sym≈ (lemma-2 (η+ c ◎ ε+ c) v)
fwd-2-coherence .(Prim id⟷) .(η- c ◎ ε- c) (rinv◎r {c = ε- c}) v = sym≈ (lemma-2 (η- c ◎ ε- c) v)
fwd-2-coherence .(Prim id⟷) .(synchl⋆ ◎ synchr⋆) (rinv◎r {c = synchr⋆}) v = sym≈ (lemma-2 synchr⋆ v)
fwd-2-coherence .(Prim id⟷) .(synchr⋆ ◎ synchl⋆) (rinv◎r {c = synchl⋆}) v = sym≈ (lemma-2 synchl⋆ v)
fwd-2-coherence .(Prim id⟷) .(app-num\\ (! c₃) ◎ app-num\\ c₃) (rinv◎r {c = app-num\\ c₃}) v = sym≈ (lemma-2 (app-num\\ c₃) v)
fwd-2-coherence .(Prim id⟷) .(app-num// (! c₃) ◎ app-num// c₃) (rinv◎r {c = app-num// c₃}) v = sym≈ (lemma-2 (app-num// c₃) v)
fwd-2-coherence .(Prim x ◎ ! (Prim x)) .(Prim id⟷) (linv◎l {c = Prim x}) v = lemma-1 (Prim x) v
fwd-2-coherence .((c ◎ c₁) ◎ ! c₁ ◎ ! c) .(Prim id⟷) (linv◎l {c = c ◎ c₁}) v = lemma-1 (c ◎ c₁) v
fwd-2-coherence .((c ⊕ c₁) ◎ (! c ⊕ ! c₁)) .(Prim id⟷) (linv◎l {c = c ⊕ c₁}) v = lemma-1 (c ⊕ c₁) v
fwd-2-coherence .(c ⊗ c₁ ◎ ! c ⊗ ! c₁) .(Prim id⟷) (linv◎l {c = c ⊗ c₁}) v = lemma-1 (c ⊗ c₁) v
fwd-2-coherence .(η- c ◎ ε- c) .(Prim id⟷) (linv◎l {c = η- c}) v = lemma-1 (η- c ◎ ε- c) v
fwd-2-coherence .(η+ c ◎ ε+ c) .(Prim id⟷) (linv◎l {c = η+ c}) v = lemma-1 (η+ c ◎ ε+ c) v
fwd-2-coherence .(ε+ c ◎ η+ c) .(Prim id⟷) (linv◎l {c = ε+ c}) v = lemma-1 (ε+ c ◎ η+ c) v
fwd-2-coherence .(ε- c ◎ η- c) .(Prim id⟷) (linv◎l {c = ε- c}) v = lemma-1 (ε- c ◎ η- c) v
fwd-2-coherence .(synchr⋆ ◎ synchl⋆) .(Prim id⟷) (linv◎l {c = synchr⋆}) v = lemma-1 synchr⋆ v
fwd-2-coherence .(synchl⋆ ◎ synchr⋆) .(Prim id⟷) (linv◎l {c = synchl⋆}) v = lemma-1 synchl⋆ v
fwd-2-coherence .(app-num\\ c₃ ◎ app-num\\ (! c₃)) .(Prim id⟷) (linv◎l {c = app-num\\ c₃}) v = lemma-1 (app-num\\ c₃) v
fwd-2-coherence .(app-num// c₃ ◎ app-num// (! c₃)) .(Prim id⟷) (linv◎l {c = app-num// c₃}) v = lemma-1 (app-num// c₃) v
fwd-2-coherence .(Prim id⟷) .(Prim x ◎ ! (Prim x)) (linv◎r {c = Prim x}) v = sym≈ (lemma-1 (Prim x) v)
fwd-2-coherence .(Prim id⟷) .((c ◎ c₁) ◎ ! c₁ ◎ ! c) (linv◎r {c = c ◎ c₁}) v = sym≈ (lemma-1 (c ◎ c₁) v)
fwd-2-coherence .(Prim id⟷) .((c ⊕ c₁) ◎ (! c ⊕ ! c₁)) (linv◎r {c = c ⊕ c₁}) v = sym≈ (lemma-1 (c ⊕ c₁) v)
fwd-2-coherence .(Prim id⟷) .(c ⊗ c₁ ◎ ! c ⊗ ! c₁) (linv◎r {c = c ⊗ c₁}) v = sym≈ (lemma-1 (c ⊗ c₁) v)
fwd-2-coherence .(Prim id⟷) .(η- c ◎ ε- c) (linv◎r {c = η- c}) v = sym≈ (lemma-1 (η- c ◎ ε- c) v)
fwd-2-coherence .(Prim id⟷) .(η+ c ◎ ε+ c) (linv◎r {c = η+ c}) v = sym≈ (lemma-1 (η+ c ◎ ε+ c) v)
fwd-2-coherence .(Prim id⟷) .(ε+ c ◎ η+ c) (linv◎r {c = ε+ c}) v = sym≈ (lemma-1 (ε+ c ◎ η+ c) v)
fwd-2-coherence .(Prim id⟷) .(ε- c ◎ η- c) (linv◎r {c = ε- c}) v = sym≈ (lemma-1 (ε- c ◎ η- c) v)
fwd-2-coherence .(Prim id⟷) .(synchr⋆ ◎ synchl⋆) (linv◎r {c = synchr⋆}) v = sym≈ (lemma-1 synchr⋆ v)
fwd-2-coherence .(Prim id⟷) .(synchl⋆ ◎ synchr⋆) (linv◎r {c = synchl⋆}) v = sym≈ (lemma-1 synchl⋆ v)
fwd-2-coherence .(Prim id⟷) .(app-num\\ c₃ ◎ app-num\\ (! c₃)) (linv◎r {c = app-num\\ c₃}) v = sym≈ (lemma-1 (app-num\\ c₃) v)
fwd-2-coherence .(Prim id⟷) .(app-num// c₃ ◎ app-num// (! c₃)) (linv◎r {c = app-num// c₃}) v = sym≈ (lemma-1 (app-num// c₃) v)
fwd-2-coherence c₁ c₂ (p₁ ● p₂) v =
  trans≈ (fwd-2-coherence _ _ p₁ v) (fwd-2-coherence _ _ p₂ v)
fwd-2-coherence _ _ (_⊡_ {c₁ = c₁} {c₃ = c₃} {c₄ = c₄} p₁ p₂) v =
  trans≈ (fwd-2-coherence _ _ p₂ (𝓐𝓹 c₁ v)) (cong≈ c₄ (fwd-2-coherence _ _ p₁ v))
fwd-2-coherence _ _ (resp⊕⇔ p₁ p₂) (inl v) = inj≈ (fwd-2-coherence _ _ p₁ v)
fwd-2-coherence _ _ (resp⊕⇔ p₁ p₂) (inr v) = inj≈ (fwd-2-coherence _ _ p₂ v)
fwd-2-coherence _ _ (resp⊗⇔ p₁ p₂) [ v₁ , v₂ ] = [,]≈ (fwd-2-coherence _ _ p₁ v₁) (fwd-2-coherence _ _ p₂ v₂)
fwd-2-coherence _ _ (resp-app-num// p) (tangr x) = {!!}
fwd-2-coherence _ _ (resp-app-num\\ p) (tangl x) = {!!}
fwd-2-coherence c₁ c₂ (lift# x) v = {!!}
fwd-2-coherence _ _ (lift#! x) v = {!!}

------
-- Examples
BOOL : U
BOOL = 𝟙 ⊕ 𝟙

NOT : BOOL ⟷ BOOL
NOT = Prim swap₊

-- cc-like
cc : # NOT ⟷ # NOT
cc = Prim uniti⋆l ◎
     (((η+ NOT) ⊗ Prim id⟷) ◎ 
     ((synchr⋆ ◎ 
     ((Prim id⟷ ⊗ (ε- NOT)) )))) ◎
     Prim unite⋆r

i₀ i₁ : Iter NOT
i₀ = zeroth NOT -- essentially id⟷
i₁ = iter NOT   -- essentially swap⋆

v₀ v₁ : Val (# NOT)
v₀ = comb i₀
v₁ = comb i₁

cc₁ cc₂ : Val (# NOT)
cc₁ = 𝓐𝓹 cc v₀ -- evaluates to v₀, on the nose
cc₂ = 𝓐𝓹 cc v₁ -- evaluates to v₁, on the nose

--------------------------------
-- Various things to check out
zig-zag : ∀ {t : U} {c : t ⟷ t} → # c ⟷ # c
zig-zag {_} {c} = Prim uniti⋆l ◎ η+ c ⊗ (Prim id⟷) ◎ synchr⋆ ◎ (Prim id⟷ ⊗ ε- c) ◎ Prim unite⋆r

zig-zag-prop : {t : U} {c : t ⟷ t} (v : Val (# c)) → 𝓐𝓹 zig-zag v ≈ v
zig-zag-prop (comb x) = refl≈ refl

--------------------------------
-- To define trace, what we're missing is a combinator which goes from
-- (f : s ⊗ # c ⟷ s ⊗ # c) to t ⊗ (c // c) ⟷ u ⊗ (c // c)

-- trace : {s t u : U} {c : s ⟷ s} → (f : s ⊗ # c ⟷ s ⊗ # c) → t ⟷ u
-- trace {s} {t} {u} {c = c} f =
--   Prim (uniti⋆r {t}) ◎ (Prim id⟷ ⊗ η+ c) ◎ {!!} ◎ (Prim id⟷ ⊗ ε+ c) ◎ Prim unite⋆r

