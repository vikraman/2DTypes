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
