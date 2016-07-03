{-# OPTIONS --without-K #-}

module 2D.opsem3 where

open import Data.Sum hiding ([_,_])
open import Data.Product hiding (<_,_>;,_;_,_)

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
  𝓐𝓹 (η- c) (𝟙ₚ x) = [ (1/comb ⟪ c , id⇔ ⟫) , (comb x) ]
  𝓐𝓹 (η+ c) (𝟙ₚ x) = [ (comb x) , (1/comb ⟪ c , id⇔ ⟫) ]
  𝓐𝓹 (ε+ c) [ comb x , 1/comb x₁ ] = 𝟙ₚ x
  𝓐𝓹 (ε- c) [ 1/comb x , comb x₁ ] = 𝟙ₚ x₁
  𝓐𝓹 (unite⋆l# c) [ 𝟙ₚ < i , _ , _ > , comb x₁ ] = [ 𝟙ₚ < i , Prim id⟷ , 2! (id^i⇔id i) > , comb x₁ ]
  𝓐𝓹 (uniti⋆l# c) [ 𝟙ₚ < k , q , α > , comb x ] = [ (𝟙ₚ < k , (c ^ k) , id⇔ >) , (comb x) ]
  𝓐𝓹 (unite⋆r# c) [ v , v₁ ] = {!!}
  𝓐𝓹 (uniti⋆r# c) [ comb x , 𝟙ₚ ii ] = {!!}

  𝓐𝓹⁻¹ : {T₁ T₂ : U} → (T₁ ⟷ T₂) → Val T₂ → Val T₁
  𝓐𝓹⁻¹ (Prim x) v = prim⁻¹ x v
  𝓐𝓹⁻¹ (c ◎ c₁) v = 𝓐𝓹⁻¹ c (𝓐𝓹⁻¹ c₁ v)
  𝓐𝓹⁻¹ (c ⊕ c₁) (inl v) = inl (𝓐𝓹⁻¹ c v)
  𝓐𝓹⁻¹ (c ⊕ c₁) (inr v) = inr (𝓐𝓹⁻¹ c₁ v)
  𝓐𝓹⁻¹ (c ⊗ c₁) [ v , w ] = [ (𝓐𝓹⁻¹ c v) , (𝓐𝓹⁻¹ c₁ w) ]
  -- 𝓐𝓹⁻¹ ap⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹⁻¹ (Iter.q x) v₁) ]
  -- 𝓐𝓹⁻¹ ap⁻¹⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹 (Iter.q x) v₁) ]
  𝓐𝓹⁻¹ (η- c) [ v , comb x ] = 𝟙ₚ x
  𝓐𝓹⁻¹ (η+ c) [ comb x , v₁ ] = 𝟙ₚ x
  𝓐𝓹⁻¹ (ε+ c) (𝟙ₚ x) = [ (comb x) , (1/comb ⟪ c , id⇔ ⟫) ]
  𝓐𝓹⁻¹ (ε- c) (𝟙ₚ x) = [ (1/comb ⟪ c , id⇔ ⟫) , (comb x) ]
  𝓐𝓹⁻¹ (unite⋆l# c) [ 𝟙ₚ < k , q , α > , comb x₁ ] = [ (𝟙ₚ < k , c ^ k , id⇔ >) , (comb x₁) ]
  𝓐𝓹⁻¹ (uniti⋆l# c) [ 𝟙ₚ < k , q , α > , comb x₁ ] = [ (𝟙ₚ < k , Prim id⟷ , 2! (id^i⇔id k) >) , (comb x₁) ]
  𝓐𝓹⁻¹ (unite⋆r# c) v = {!!}
  𝓐𝓹⁻¹ (uniti⋆r# c) [ v , 𝟙ₚ x ] = {!!}

cong≈ : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) {v w : Val T₁} → v ≈ w → 𝓐𝓹 c v ≈ 𝓐𝓹 c w
cong≈ (Prim x) p = prim-cong≈ x p
cong≈ (c₁ ◎ c₂) p = cong≈ c₂ (cong≈ c₁ p)
cong≈ (c₁ ⊕ c₂) (inj₁≈ p) = inj₁≈ (cong≈ c₁ p)
cong≈ (c₁ ⊕ c₂) (inj₂≈ p) = inj₂≈ (cong≈ c₂ p)
cong≈ (c₁ ⊗ c₂) ([,]≈ p₁ p₂) = [,]≈ (cong≈ c₁ p₁) (cong≈ c₂ p₂)
-- cong≈ ap⟷ ([,]≈ (#p≈ {_} {p} (comb x) (comb x₁) x₂) p₂) =
--   [,]≈ (#p≈ (comb x) (comb x₁) x₂) ({!!})
-- cong≈ ap⁻¹⟷ ([,]≈ p₁ p₂) = {!!}
cong≈ (η- c) (𝟙ₚ≈ p q r x) = [,]≈ (refl≈ refl) (#p≈ (comb q) (comb r) x)
cong≈ (η+ c) (𝟙ₚ≈ p₁ q r x) = [,]≈ (#p≈ (comb q) (comb r) x) (refl≈ refl)
cong≈ (ε+ c) ([,]≈ (#p≈ (comb x) (comb x₁) x₂) (1/#p≈ q p₁ p₂ x₃)) = 𝟙ₚ≈ q x x₁ x₂
cong≈ (ε- p) ([,]≈ (1/#p≈ q p₁ p₂ x₂) (#p≈ (comb x) (comb x₁) x₃)) = 𝟙ₚ≈ q x x₁ x₃
cong≈ (unite⋆l# p) ([,]≈ (𝟙ₚ≈ p₁ q r x₂) (#p≈ (comb x) (comb x₁) x₃)) =
  [,]≈ (𝟙ₚ≈ {!!} {!!} {!!} idl◎l) (#p≈ (comb x) (comb x₁) x₃)
cong≈ (uniti⋆l# p) eq = {!!}
cong≈ (unite⋆r# c) ([,]≈ p₁ p₂) = {!!}
cong≈ (uniti⋆r# p) eq = {!!}

cong⁻¹≈ : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → {v w : Val T₂} → v ≈ w → 𝓐𝓹⁻¹ c v ≈ 𝓐𝓹⁻¹ c w
cong⁻¹≈ (Prim x) p = prim⁻¹-cong≈ x p
cong⁻¹≈ (c₁ ◎ c₂) p = cong⁻¹≈ c₁ (cong⁻¹≈ c₂ p)
cong⁻¹≈ (c₁ ⊕ c₂) (inj₁≈ p) = inj₁≈ (cong⁻¹≈ c₁ p)
cong⁻¹≈ (c₁ ⊕ c₂) (inj₂≈ p) = inj₂≈ (cong⁻¹≈ c₂ p)
cong⁻¹≈ (c₁ ⊗ c₂) ([,]≈ p₁ p₂) = [,]≈ (cong⁻¹≈ c₁ p₁) (cong⁻¹≈ c₂ p₂)
-- cong⁻¹≈ ap⟷ ([,]≈ p₁ p₂) = {!!}
-- cong⁻¹≈ ap⁻¹⟷ ([,]≈ p₁ p₂) = {!!}
cong⁻¹≈ (η- p) ([,]≈ (1/#p≈ q p₁ p₂ x₂) (#p≈ (comb x) (comb x₁) x₃)) = 𝟙ₚ≈ q x x₁ x₃
cong⁻¹≈ (η+ p) ([,]≈ (#p≈ (comb x) (comb x₁) x₂) (1/#p≈ q p₁ p₂ x₃)) = 𝟙ₚ≈ q x x₁ x₂
cong⁻¹≈ (ε+ c) (𝟙ₚ≈ p q r x) = [,]≈ (#p≈ (comb q) (comb r) x) (refl≈ refl)
cong⁻¹≈ (ε- c) (𝟙ₚ≈ p q r x) = [,]≈ (refl≈ refl) (#p≈ (comb q) (comb r) x)
cong⁻¹≈ (unite⋆l# p) eq = {!!}
cong⁻¹≈ (uniti⋆l# p) ([,]≈ (𝟙ₚ≈ p₁ q r x) p₂) = {!!}
cong⁻¹≈ (unite⋆r# p) eq = {!!}
cong⁻¹≈ (uniti⋆r# p) ([,]≈ p₁ (𝟙ₚ≈ p₂ q r x)) = {!!}

mutual
  fwd◎bwd≈id : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : Val T₂) → (𝓐𝓹 c (𝓐𝓹⁻¹ c v)) ≈ v
  fwd◎bwd≈id (Prim x) v = refl≈ (prim◎prim⁻¹≡id x v)
  fwd◎bwd≈id (c ◎ c₁) v = trans≈ (cong≈ c₁ (fwd◎bwd≈id c (𝓐𝓹⁻¹ c₁ v))) (fwd◎bwd≈id c₁ v)
  fwd◎bwd≈id (c ⊕ c₁) (inl v) = inj₁≈ (fwd◎bwd≈id c v)
  fwd◎bwd≈id (c ⊕ c₁) (inr v) = inj₂≈ (fwd◎bwd≈id c₁ v)
  fwd◎bwd≈id (c ⊗ c₁) [ v , v₁ ] = [,]≈ (fwd◎bwd≈id c v) (fwd◎bwd≈id c₁ v₁)
--   fwd◎bwd≈id ap⟷ [ comb {t} {p} < i , q , α > , v₁ ] =
--     [,]≈ (#p≈ (comb < i , q , α >) (comb < i , q , α >) linv◎l)
--          (fwd◎bwd≈id q v₁)
--   fwd◎bwd≈id ap⁻¹⟷ [ comb x , v₁ ] = [,]≈ (refl≈ refl) (bwd◎fwd≈id (Iter.q x) v₁)
  fwd◎bwd≈id (η- c) [ 1/comb x , comb x₁ ] =
    [,]≈ (1/#p≈ x₁ (sing c) x (id⇔ ⊡ ⇔! (Sing.eq x) ● linv◎l ● linv◎r))
         (refl≈ refl)
  fwd◎bwd≈id (η+ c) [ comb x , 1/comb x₁ ] =
    [,]≈ (refl≈ refl)
         (1/#p≈ x (sing c) x₁ ((id⇔ ⊡ ⇔! (Sing.eq x₁) ● linv◎l ● linv◎r)))
  fwd◎bwd≈id (ε+ c) (𝟙ₚ x) = refl≈ refl -- trivial
    -- note that this means that we get x back on the nose.
  fwd◎bwd≈id (ε- c) (𝟙ₚ x) = refl≈ refl -- 𝟙ₚ≈ {p₁ = x} {x} x x id⇔
  fwd◎bwd≈id (unite⋆l# c) v = {!!} -- refl≈ refl
  fwd◎bwd≈id (uniti⋆l# c) [ 𝟙ₚ < i , q , α > , comb x ] = {!!}
  fwd◎bwd≈id (unite⋆r# c) v = {!!} -- refl≈ refl
  fwd◎bwd≈id (uniti⋆r# c) [ comb x , 𝟙ₚ < i , q , α > ] = {!!}

  bwd◎fwd≈id : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : Val T₁) → (𝓐𝓹⁻¹ c (𝓐𝓹 c v)) ≈ v
  bwd◎fwd≈id (Prim x) v = refl≈ (prim⁻¹◎prim≡id x v)
  bwd◎fwd≈id (c ◎ c₁) v = trans≈ (cong⁻¹≈ c (bwd◎fwd≈id c₁ (𝓐𝓹 c v))) (bwd◎fwd≈id c v)
  bwd◎fwd≈id (c ⊕ c₁) (inl v) = inj₁≈ (bwd◎fwd≈id c v)
  bwd◎fwd≈id (c ⊕ c₁) (inr v) = inj₂≈ (bwd◎fwd≈id c₁ v)
  bwd◎fwd≈id (c ⊗ c₁) [ v , v₁ ] = [,]≈ (bwd◎fwd≈id c v) (bwd◎fwd≈id c₁ v₁)
--   bwd◎fwd≈id ap⟷ [ comb x , v₁ ] = [,]≈ (refl≈ refl) (bwd◎fwd≈id (Iter.q x) v₁)
--   bwd◎fwd≈id ap⁻¹⟷ [ comb {t} {p} < i , q , α > , v₁ ] =
--     [,]≈ (#p≈ (comb < i , q , α >) (comb < i , q , α >) linv◎l)
--          (fwd◎bwd≈id q v₁)
  bwd◎fwd≈id (η- c) (𝟙ₚ x) = refl≈ refl
  bwd◎fwd≈id (η+ c) (𝟙ₚ x) = refl≈ refl
  bwd◎fwd≈id (ε+ c) [ comb < k , q , α > , 1/comb ⟪ p' , eq ⟫ ] =
    [,]≈ (refl≈ refl)
         (1/#p≈ < k , q , α > ⟪ c , id⇔ ⟫ ⟪ p' , eq ⟫ (id⇔ ⊡ (⇔! eq) ● linv◎l ● linv◎r))
  bwd◎fwd≈id (ε- c) [ 1/comb ⟪ p' , eq ⟫ , comb < k , q , α > ] =
    [,]≈ (1/#p≈ < k , q , α > ⟪ c , id⇔ ⟫ ⟪ p' , eq ⟫ ((id⇔ ⊡ (⇔! eq) ● linv◎l ● linv◎r)))
         (refl≈ refl)
  bwd◎fwd≈id (unite⋆l# c) [ 𝟙ₚ < i , q , α > , comb x ] = [,]≈ (𝟙ₚ≈ x < i , c ^ i , id⇔ > < i , q , α > ((2! α) ⊡ id⇔ ● linv◎l)) (refl≈ refl)
  bwd◎fwd≈id (uniti⋆l# c) [ 𝟙ₚ < k , q , α > , comb x₁ ] = {!!}
  bwd◎fwd≈id (unite⋆r# c) [ v , 𝟙ₚ < i , q , α > ] = {!!}
  bwd◎fwd≈id (uniti⋆r# c) [ comb x , 𝟙ₚ x₁ ] = {!!} -- refl≈ refl

bwd-coherence : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : Val T₂) → 𝓐𝓹⁻¹ c v ≈ 𝓐𝓹 (! c) v
bwd-coherence c v = {!!}

------
-- Examples
BOOL : U
BOOL = 𝟙 ⊕ 𝟙

NOT : BOOL ⟷ BOOL
NOT = Prim swap₊

-- cc-like
cc : (𝟙# NOT ⊗ # NOT) ⟷ (# NOT ⊗ 𝟙# NOT)
cc = (((η+ NOT) ⊗ Prim id⟷) ◎     -- (# NOT ⊗ 1/# NOT) ⊗ # NOT
     ((Prim assocr⋆ ◎               -- # NOT ⊗ (1/# NOT ⊗ # NOT)
     ((Prim id⟷ ⊗ Prim swap⋆) ◎    --   # NOT ⊗ # NOT ⊗ 1/# NOT
     ((Prim id⟷ ⊗ (ε+ NOT)) )))))  -- # NOT ⊗ 1# NOT

i₀ i₁ : Iter NOT
i₀ = zeroth NOT
i₁ = iter NOT

v₁ v₂ v₃ v₄ : Val (𝟙# NOT ⊗ # NOT)
v₁ = [ 𝟙ₚ i₀ , comb i₀ ] 
v₂ = [ 𝟙ₚ i₁ , comb i₀ ] 
v₃ = [ 𝟙ₚ i₀ , comb i₁ ] 
v₄ = [ 𝟙ₚ i₁ , comb i₁ ] 

cc₁ cc₂ cc₃ cc₄ : Val (# NOT ⊗ 𝟙# NOT)
cc₁ = 𝓐𝓹 cc v₁
  -- evaluates to v₁
cc₂ = 𝓐𝓹 cc v₂
  -- evaluates to v₂
cc₃ = 𝓐𝓹 cc v₃
  -- evauates to v₃
cc₄ = 𝓐𝓹 cc v₄
  -- evaluates to v₄
