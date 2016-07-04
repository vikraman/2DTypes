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
  𝓐𝓹 (η- c) (𝟙ₚ (si i eq)) = [ (1/comb ⟪ c , id⇔ ⟫) , comb < i , c ^ i , id⇔ > ]
  𝓐𝓹 (η+ c) (𝟙ₚ (si i eq)) = [ (comb < i , (c ^ i) , id⇔ >) , (1/comb ⟪ c , id⇔ ⟫) ]
  𝓐𝓹 (ε+ c) [ comb < k , q , α > , 1/comb x₁ ] = 𝟙ₚ (si k α)
  𝓐𝓹 (ε- c) [ 1/comb x , comb < k , q , α > ] = 𝟙ₚ (si k α)
--   𝓐𝓹 (unite⋆l# c) [ 𝟙ₚ (si j β) , comb < k , q₁ , α₁ > ] =
--     comb < k , q₁ , α₁ >
--   𝓐𝓹 (uniti⋆l# c) (comb < k₁ , q₁ , α₁ > ) =
--     [ (𝟙ₚ (si k₁ α₁)) , (comb < k₁ , q₁ , α₁ >) ]
--   𝓐𝓹 (unite⋆r# c) [ x , 𝟙ₚ s ] = x
--   𝓐𝓹 (uniti⋆r# c) (comb < k , q , α >) = [ (comb < k , q , α >) , (𝟙ₚ (si k α)) ]
  𝓐𝓹 (name {_} {c} f) (𝟙ₚ (si i eq)) = [ (1/comb ⟪ c , id⇔ ⟫) , 𝓐𝓹 f (comb < i , c ^ i , id⇔ > ) ]
  𝓐𝓹 (coname {_} {c} f) [ x , comb < k , q , α > ] =
    let w = 𝓐𝓹⁻¹ f (comb < k , q , α >) in
    case w of λ { (comb < i , r , β > ) → 𝟙ₚ (si i β) }

  𝓐𝓹⁻¹ : {T₁ T₂ : U} → (T₁ ⟷ T₂) → Val T₂ → Val T₁
  𝓐𝓹⁻¹ (Prim x) v = prim⁻¹ x v
  𝓐𝓹⁻¹ (c ◎ c₁) v = 𝓐𝓹⁻¹ c (𝓐𝓹⁻¹ c₁ v)
  𝓐𝓹⁻¹ (c ⊕ c₁) (inl v) = inl (𝓐𝓹⁻¹ c v)
  𝓐𝓹⁻¹ (c ⊕ c₁) (inr v) = inr (𝓐𝓹⁻¹ c₁ v)
  𝓐𝓹⁻¹ (c ⊗ c₁) [ v , w ] = [ (𝓐𝓹⁻¹ c v) , (𝓐𝓹⁻¹ c₁ w) ]
  -- 𝓐𝓹⁻¹ ap⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹⁻¹ (Iter.q x) v₁) ]
  -- 𝓐𝓹⁻¹ ap⁻¹⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹 (Iter.q x) v₁) ]
  𝓐𝓹⁻¹ (η- c) [ 1/comb x , comb < k , q , α > ] = 𝟙ₚ (si k α)
  𝓐𝓹⁻¹ (η+ c) [ comb < k , q , α > , v₁ ] = 𝟙ₚ (si k α)
  𝓐𝓹⁻¹ (ε+ c) (𝟙ₚ (si k α)) = [ (comb < k , c ^ k , id⇔ >) , (1/comb ⟪ c , id⇔ ⟫) ]
  𝓐𝓹⁻¹ (ε- c) (𝟙ₚ (si k _)) = [ (1/comb ⟪ c , id⇔ ⟫) , (comb < k , (c ^ k) , id⇔ >) ]
--   𝓐𝓹⁻¹ (unite⋆l# c) (comb < k , q , α >) = [ (𝟙ₚ (si k α)) , (comb < k , q , α >) ]
--   𝓐𝓹⁻¹ (uniti⋆l# c) [ 𝟙ₚ s , comb x₁ ] = (comb x₁)
--   𝓐𝓹⁻¹ (unite⋆r# c) (comb < k , q , α >) = [ (comb < k , q , α >) , (𝟙ₚ (si k α)) ]
--   𝓐𝓹⁻¹ (uniti⋆r# c) [ comb x , 𝟙ₚ s ] = comb x
  𝓐𝓹⁻¹ (name f) [ x , comb < k , q , α > ] = 
    let w = 𝓐𝓹⁻¹ f (comb < k , q , α >) in
    case w of λ { (comb < i , r , β > ) → 𝟙ₚ (si i β) }
  𝓐𝓹⁻¹ (coname {_} {c} f) (𝟙ₚ (si i eq)) =  [ (1/comb ⟪ c , id⇔ ⟫) , 𝓐𝓹 f (comb < i , c ^ i , id⇔ > ) ]

cong≈ : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) {v w : Val T₁} → v ≈ w → 𝓐𝓹 c v ≈ 𝓐𝓹 c w
cong≈ (Prim x) p = prim-cong≈ x p
cong≈ (c₁ ◎ c₂) p = cong≈ c₂ (cong≈ c₁ p)
cong≈ (c₁ ⊕ c₂) (inj₁≈ p) = inj₁≈ (cong≈ c₁ p)
cong≈ (c₁ ⊕ c₂) (inj₂≈ p) = inj₂≈ (cong≈ c₂ p)
cong≈ (c₁ ⊗ c₂) ([,]≈ p₁ p₂) = [,]≈ (cong≈ c₁ p₁) (cong≈ c₂ p₂)
-- cong≈ ap⟷ ([,]≈ (#p≈ {_} {p} (comb x) (comb x₁) x₂) p₂) =
--   [,]≈ (#p≈ (comb x) (comb x₁) x₂) ({!!})
-- cong≈ ap⁻¹⟷ ([,]≈ p₁ p₂) = {!!}
cong≈ (η- c) (𝟙ₚ≈ p₁ {p₂} eq {si i α} {si j β}) =
  [,]≈ (refl≈ refl)
       (#p≈ (comb < i , c ^ i , id⇔ >)
            (comb < j , c ^ j , id⇔ >)
            ((2! α) ⊡ (⇔! (2! β)) ● eq ⊡ id⇔ ● linv◎l))
cong≈ (η+ c) (𝟙ₚ≈ p₁ {p₂} eq {si i α} {si j β}) =
  [,]≈ (#p≈ (comb < i , c ^ i , id⇔ >)
            (comb < j , c ^ j , id⇔ >)
            ((2! α) ⊡ (⇔! (2! β)) ● eq ⊡ id⇔ ● linv◎l))
       (refl≈ refl)
cong≈ (ε+ c) ([,]≈ (#p≈ (comb < k , q , α >) (comb < k₁ , q₁ , α₁ >) x₂) (1/#p≈ q₂ p₁ p₂ x₃)) =
  𝟙ₚ≈ q (inverse⇒⇔ x₂)
cong≈ (ε- p) ([,]≈ (1/#p≈ q p₁ p₂ x₂) (#p≈ (comb x) (comb x₁) x₃)) = 𝟙ₚ≈ (Iter.q x) (inverse⇒⇔ x₃)
-- cong≈ (unite⋆l# p) ([,]≈ (𝟙ₚ≈ q) (#p≈ (comb x) (comb x₁) x₃)) = #p≈ (comb x) (comb x₁) x₃
-- cong≈ (uniti⋆l# p) (#p≈ (comb < k , q , α >) (comb < k₁ , q₁ , α₁ >) x₂) =
--   [,]≈ (𝟙ₚ≈ q) (#p≈ (comb < k , q , α >) (comb < k₁ , q₁ , α₁ >) x₂)
-- cong≈ (unite⋆r# p) ([,]≈ (#p≈ (comb x) (comb x₁) x₂) (𝟙ₚ≈ p₁)) = #p≈ (comb x) (comb x₁) x₂
-- cong≈ (uniti⋆r# p) (#p≈ (comb x) (comb x₁) x₂) = {!!}
cong≈ (name f) (𝟙ₚ≈ {_} {c} p₁ equiv {si i α} {si j β}) =
  [,]≈ (refl≈ refl)
       (cong≈ f (#p≈ (comb < i , c ^ i , id⇔ >) (comb < j , (c ^ j) , id⇔ >) (2! α ⊡ (⇔! (2! β)) ● (equiv ⊡ id⇔) ● linv◎l)))
cong≈ (coname f) ([,]≈ (1/#p≈ q₂ p₁ p₂ x₂) (#p≈ (comb < k , q , α >) (comb < k₁ , q₁ , α₁ >) x₃)) with 𝓐𝓹⁻¹ f (comb < k , q , α > ) | inspect (𝓐𝓹⁻¹ f) (comb < k , q , α > ) | 𝓐𝓹⁻¹ f (comb < k₁ , q₁ , α₁ >) | inspect (𝓐𝓹⁻¹ f) (comb < k₁ , q₁ , α₁ >)
... | comb < i , r , β > | [ eq ] | comb < j , s , γ > | [ eq₂ ] = 𝟙ₚ≈ {!!} {!!}

cong⁻¹≈ : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → {v w : Val T₂} → v ≈ w → 𝓐𝓹⁻¹ c v ≈ 𝓐𝓹⁻¹ c w
cong⁻¹≈ (Prim x) p = prim⁻¹-cong≈ x p
cong⁻¹≈ (c₁ ◎ c₂) p = cong⁻¹≈ c₁ (cong⁻¹≈ c₂ p)
cong⁻¹≈ (c₁ ⊕ c₂) (inj₁≈ p) = inj₁≈ (cong⁻¹≈ c₁ p)
cong⁻¹≈ (c₁ ⊕ c₂) (inj₂≈ p) = inj₂≈ (cong⁻¹≈ c₂ p)
cong⁻¹≈ (c₁ ⊗ c₂) ([,]≈ p₁ p₂) = [,]≈ (cong⁻¹≈ c₁ p₁) (cong⁻¹≈ c₂ p₂)
-- cong⁻¹≈ ap⟷ ([,]≈ p₁ p₂) = {!!}
-- cong⁻¹≈ ap⁻¹⟷ ([,]≈ p₁ p₂) = {!!}
cong⁻¹≈ (η- p) ([,]≈ (1/#p≈ q p₁ p₂ x₂) (#p≈ (comb x) (comb x₁) x₃)) = 𝟙ₚ≈ (Iter.q x) (inverse⇒⇔ x₃)
cong⁻¹≈ (η+ p) ([,]≈ (#p≈ (comb x) (comb x₁) x₂) (1/#p≈ q p₁ p₂ x₃)) = 𝟙ₚ≈ (Iter.q x) (inverse⇒⇔ x₂)
cong⁻¹≈ (ε+ c) (𝟙ₚ≈ p₁ {p₂} eq {si i α} {si j β}) =
  [,]≈ (#p≈ (comb < i , c ^ i , id⇔ >)
            (comb < j , c ^ j , id⇔ >)
            ((2! α) ⊡ (⇔! (2! β)) ● eq ⊡ id⇔ ● linv◎l))
       (refl≈ refl)
cong⁻¹≈ (ε- c) (𝟙ₚ≈ p₁ {p₂} eq {si i α} {si j β}) =
  [,]≈  (refl≈ refl)
        (#p≈ (comb < i , c ^ i , id⇔ >)
            (comb < j , c ^ j , id⇔ >)
            ((2! α) ⊡ (⇔! (2! β)) ● eq ⊡ id⇔ ● linv◎l))      
-- cong⁻¹≈ (unite⋆l# p) eq = {!!}
-- cong⁻¹≈ (uniti⋆l# p) ([,]≈ (𝟙ₚ≈ p₁ q r x) p₂) = {!!}
-- cong⁻¹≈ (unite⋆r# p) eq = {!!}
-- cong⁻¹≈ (uniti⋆r# p) ([,]≈ p₁ (𝟙ₚ≈ p₂ q r x)) = {!!}
cong⁻¹≈ (name f) v = {!!}
cong⁻¹≈ (coname f) v = {!!}

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
  fwd◎bwd≈id (η- c) [ 1/comb ⟪ x , β ⟫ , comb < k , q , α > ] =
    [,]≈ (1/#p≈ < k , q , α > ⟪ c , id⇔ ⟫ ⟪ x , β ⟫ (2! β ⊡ id⇔ ● linv◎l ● linv◎r))
        (#p≈ (comb < k , c ^ k , id⇔ >) (comb < k , q , α >) (2! α ⊡ id⇔ ● linv◎l))
  fwd◎bwd≈id (η+ c) [ comb < k , q , α > , 1/comb x₁ ] =
    [,]≈ (#p≈ (comb < k , c ^ k , id⇔ >) (comb < k , q , α >) (2! α ⊡ id⇔ ● linv◎l))
        (1/#p≈ < k , q , α > ⟪ c , id⇔ ⟫ x₁ (2! (Sing.eq x₁) ⊡ id⇔ ● linv◎l ● linv◎r))
  fwd◎bwd≈id (ε+ c) (𝟙ₚ (si i eq)) = 𝟙ₚ≈ (c ^ i) (2! eq)
  fwd◎bwd≈id (ε- c) (𝟙ₚ (si i eq)) = 𝟙ₚ≈ (c ^ i) (2! eq)
  -- fwd◎bwd≈id (unite⋆l# c) v = {!!} -- refl≈ refl
  -- fwd◎bwd≈id (uniti⋆l# c) [ 𝟙ₚ q , comb x ] = {!!}
  -- fwd◎bwd≈id (unite⋆r# c) v = {!!} -- refl≈ refl
  -- fwd◎bwd≈id (uniti⋆r# c) [ comb x , 𝟙ₚ s ] = {!!}
  fwd◎bwd≈id (name f) [ 1/comb x , comb < k , q , α > ] = {!!}
  fwd◎bwd≈id (coname f) (𝟙ₚ {_} {c} (si i eq)) with 𝓐𝓹 f (comb < i , c ^ i , id⇔ >) | inspect (𝓐𝓹 f) (comb < i , c ^ i , id⇔ >)
  ... | comb < k , q , α > | [ eq₀ ] with 𝓐𝓹⁻¹ f (comb < k , q , α >) | inspect (𝓐𝓹⁻¹ f) (comb < k , q , α >)
  ... | comb < j , r , β > | [ eq₁ ] = let pf = trans≈ (sym≈ (bwd◎fwd≈id f (comb < i , c ^ i , id⇔ >)))
                                                  (trans≈ (cong⁻¹≈ f (refl≈ eq₀)) (refl≈ eq₁)) in
                                        let eq₂ = get-equiv pf in
                                        𝟙ₚ≈ r (2! (inverse⇒⇔ (eq ⊡ id⇔ ● eq₂)))

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
  bwd◎fwd≈id (η- c) (𝟙ₚ (si i eq)) = 𝟙ₚ≈ (c ^ i) (2! eq)
  bwd◎fwd≈id (η+ c) (𝟙ₚ (si i eq)) = 𝟙ₚ≈ (c ^ i) (2! eq)
  bwd◎fwd≈id (ε+ c) [ comb < k , q , α > , 1/comb ⟪ p' , eq ⟫ ] =
    [,]≈ (#p≈ (comb < k , c ^ k , id⇔ >) (comb < k , q , α >)
         ((2! α) ⊡ id⇔ ● linv◎l)) (1/#p≈ < k , q , α > ⟪ c , id⇔ ⟫ ⟪ p' , eq ⟫ ((2! eq) ⊡ id⇔ ● linv◎l ● linv◎r))
  bwd◎fwd≈id (ε- c) [ 1/comb ⟪ p' , eq ⟫ , comb < k , q , α > ] =
    [,]≈ (1/#p≈ < k , q , α > ⟪ c , id⇔ ⟫ ⟪ p' , eq ⟫ (id⇔ ⊡ (⇔! eq) ● linv◎l ● linv◎r))
         (#p≈ (comb < k , c ^ k , id⇔ >) (comb < k , q , α >) (2! α ⊡ id⇔ ● linv◎l) )
  -- bwd◎fwd≈id (unite⋆l# c) [ 𝟙ₚ {q = q} (si k eq) , comb < j , r , β > ] =
  --   [,]≈ (𝟙ₚ≈ r) (#p≈ (comb < j , r , β >) (comb < j , r , β >) linv◎l)
  -- bwd◎fwd≈id (uniti⋆l# c) (comb x) = #p≈ (comb x) (comb x) linv◎l
  -- bwd◎fwd≈id (unite⋆r# c) [ comb x , 𝟙ₚ x₁ ] = [,]≈ (refl≈ refl) (𝟙ₚ≈ (Iter.q x))
  -- bwd◎fwd≈id (uniti⋆r# c) (comb x) = refl≈ refl
  bwd◎fwd≈id (name f) v = {!!}
  bwd◎fwd≈id (coname f) v = {!!}

bwd-coherence : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : Val T₂) → 𝓐𝓹⁻¹ c v ≈ 𝓐𝓹 (! c) v
bwd-coherence (Prim unite₊l) v = inj₂≈ (refl≈ refl)
bwd-coherence (Prim uniti₊l) (inl ())
bwd-coherence (Prim uniti₊l) (inr v) = refl≈ refl
bwd-coherence (Prim unite₊r) v = inj₁≈ (refl≈ refl)
bwd-coherence (Prim uniti₊r) (inl v) = refl≈ refl
bwd-coherence (Prim uniti₊r) (inr ())
bwd-coherence (Prim swap₊) (inl v) = inj₂≈ (bwd-coherence (Prim id⟷) v)
bwd-coherence (Prim swap₊) (inr v) = inj₁≈ (bwd-coherence (Prim id⟷) v)
bwd-coherence (Prim assocl₊) (inl (inl v)) = inj₁≈ (bwd-coherence (Prim id⟷) v)
bwd-coherence (Prim assocl₊) (inl (inr v)) = inj₂≈ (bwd-coherence (Prim id⟷) (inl v))
bwd-coherence (Prim assocl₊) (inr v) = inj₂≈ (bwd-coherence (Prim id⟷) (inr v))
bwd-coherence (Prim assocr₊) (inl v) = inj₁≈ (bwd-coherence (Prim id⟷) (inl v))
bwd-coherence (Prim assocr₊) (inr (inl v)) = inj₁≈ (bwd-coherence (Prim id⟷) (inr v))
bwd-coherence (Prim assocr₊) (inr (inr v)) = inj₂≈ (bwd-coherence (Prim id⟷) v)
bwd-coherence (Prim unite⋆l) v = [,]≈ ⋆≈ (bwd-coherence (Prim id⟷) v)
bwd-coherence (Prim uniti⋆l) [ v , v₁ ] = bwd-coherence (Prim id⟷) v₁
bwd-coherence (Prim unite⋆r) v = [,]≈ (bwd-coherence (Prim id⟷) v) ⋆≈
bwd-coherence (Prim uniti⋆r) [ v , v₁ ] = bwd-coherence (Prim id⟷) v
bwd-coherence (Prim swap⋆) [ v , v₁ ] = [,]≈ (bwd-coherence (Prim id⟷) v₁) (bwd-coherence (Prim id⟷) v)
bwd-coherence (Prim assocl⋆) [ [ v , v₁ ] , v₂ ] = [,]≈ (bwd-coherence (Prim id⟷) v)
                                                     (bwd-coherence (Prim id⟷) [ v₁ , v₂ ])
bwd-coherence (Prim assocr⋆) [ v , [ v₁ , v₂ ] ] = [,]≈ (bwd-coherence (Prim id⟷) [ v , v₁ ])
                                                     (bwd-coherence (Prim id⟷) v₂)
bwd-coherence (Prim absorbr) ()
bwd-coherence (Prim absorbl) ()
bwd-coherence (Prim factorzr) [ v , v₁ ] = bwd-coherence (Prim id⟷) v₁
bwd-coherence (Prim factorzl) [ v , v₁ ] = bwd-coherence (Prim id⟷) v
bwd-coherence (Prim dist) (inl [ v , v₁ ]) = [,]≈ (bwd-coherence (Prim id⟷) (inl v))
                                               (bwd-coherence (Prim id⟷) v₁)
bwd-coherence (Prim dist) (inr [ v , v₁ ]) = [,]≈ (bwd-coherence (Prim id⟷) (inr v))
                                               (bwd-coherence (Prim id⟷) v₁)
bwd-coherence (Prim factor) [ inl v , v₁ ] = inj₁≈ (bwd-coherence (Prim id⟷) [ v , v₁ ])
bwd-coherence (Prim factor) [ inr v , v₁ ] = inj₂≈ (bwd-coherence (Prim id⟷) [ v , v₁ ])
bwd-coherence (Prim distl) (inl [ v , v₁ ]) = [,]≈ (bwd-coherence (Prim id⟷) v)
                                                (bwd-coherence (Prim id⟷) (inl v₁))
bwd-coherence (Prim distl) (inr [ v , v₁ ]) = [,]≈ (bwd-coherence (Prim id⟷) v)
                                                (bwd-coherence (Prim id⟷) (inr v₁))
bwd-coherence (Prim factorl) [ v , inl v₁ ] = inj₁≈ (bwd-coherence (Prim id⟷) [ v , v₁ ])
bwd-coherence (Prim factorl) [ v , inr v₁ ] = inj₂≈ (bwd-coherence (Prim id⟷) [ v , v₁ ])
bwd-coherence (Prim id⟷) v = refl≈ refl
bwd-coherence (c ◎ c₁) v = 
  let eq = bwd-coherence c₁ v in
  trans≈ (cong⁻¹≈ c eq) (bwd-coherence c (𝓐𝓹 (! c₁) v))
bwd-coherence (c ⊕ c₁) (inl v) = inj₁≈ (bwd-coherence c v)
bwd-coherence (c ⊕ c₁) (inr v) = inj₂≈ (bwd-coherence c₁ v)
bwd-coherence (c ⊗ c₁) [ v , v₁ ] = [,]≈ (bwd-coherence c v) (bwd-coherence c₁ v₁)
bwd-coherence (η- c) [ 1/comb x , comb x₁ ] = refl≈ refl
bwd-coherence (η+ c) [ comb x , 1/comb x₁ ] = refl≈ refl
bwd-coherence (ε+ c) (𝟙ₚ (si i eq)) = refl≈ refl
bwd-coherence (ε- c) (𝟙ₚ (si i eq)) = refl≈ refl
bwd-coherence (name f) [ v , comb < k , q , α > ] with 𝓐𝓹⁻¹ f (comb < k , q , α >)
... | comb < i , r , β > = refl≈ refl
bwd-coherence (coname f) (𝟙ₚ (si i eq)) = refl≈ refl

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

s₀ : SingI {BOOL} {NOT} (Prim id⟷)
s₀ = si (+ 0) id⇔

s₁ : SingI {BOOL} {NOT} (NOT)
s₁ = si (+ 1) idr◎r

i₀ i₁ : Iter NOT
i₀ = zeroth NOT -- essentially id⟷
i₁ = iter NOT   -- essentially swap⋆

v₁ v₂ : Val (𝟙# NOT ⊗ # NOT)
v₁ = [ 𝟙ₚ s₁ , comb i₀ ] 
v₂ = [ 𝟙ₚ s₁ , comb i₁ ] 

v₃ v₄ : Val (# NOT ⊗ 𝟙# NOT)
v₃ = [ comb i₁ , 𝟙ₚ s₀ ] -- note how 𝟙ₚ s₀ is of type 𝟙# NOT.  The type that matters is the {NOT}
v₄ = [ comb i₁ , 𝟙ₚ s₁ ]

cc₁ cc₂ : Val (# NOT ⊗ 𝟙# NOT)
cc₁ = 𝓐𝓹 cc v₁
  -- evaluates to [ comb < + 1 , Prim swap₊ ◎ Prim id⟷ , id⇔ > , 𝟙ₚ (si (+ 0) id⇔) ]
  -- which is v₃, but not quite on the nose
cc₂ = 𝓐𝓹 cc v₂
  -- evaluates to v₄ which is also swap⋆ v₂, again not quite on the nose

eq₁ : cc₁ ≈ v₃
eq₁ = [,]≈ (#p≈ (comb < + 1 , Prim swap₊ ◎ Prim id⟷ , id⇔ >) (comb < + 1 , Prim swap₊ , idr◎r >)  (idr◎l ⊡ id⇔ ● rinv◎l)) (refl≈ refl)

eq₂ : cc₂ ≈ v₄
eq₂ = [,]≈ (#p≈ (comb < + 1 , Prim swap₊ ◎ Prim id⟷ , id⇔ >) (comb < + 1 , Prim swap₊ , idr◎r >) (idr◎l ⊡ id⇔ ● rinv◎l)) (refl≈ refl)
