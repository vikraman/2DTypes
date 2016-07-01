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
  using (_≡_; refl; trans; subst; cong; sym; cong₂)

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

-- don't know why the TERMINATING is still needed.  Will investigate later.
mutual
  {-# TERMINATING #-}
  𝓐𝓹 : {T₁ T₂ : U} → (T₁ ⟷ T₂) → Val T₁ → Val T₂
  𝓐𝓹 (Prim x) v = prim x v
  𝓐𝓹 (c ◎ c₁) v =
    let x = 𝓐𝓹 c v in 𝓐𝓹 c₁ x
  𝓐𝓹 (c ⊕ c₁) (inl v) = inl (𝓐𝓹 c v)
  𝓐𝓹 (c ⊕ c₁) (inr v) = inr (𝓐𝓹 c₁ v)
  𝓐𝓹 (c ⊗ c₁) [ v , w ] = [ 𝓐𝓹 c v , 𝓐𝓹 c₁ w ]
  𝓐𝓹 foldSwap (inl v) = comb < (+ 0) , (Prim id⟷) , id⇔ >
  𝓐𝓹 foldSwap (inr v) = comb < (+ 1) , (Prim swap₊) , idr◎r >
  𝓐𝓹 unfoldSwap (comb < k , q , α >) = Fin2⇒1+1 (mod2 k)
  𝓐𝓹 ap⟷ [ comb < i , q , α > , v₁ ] = [ (comb < i , q , α >) , (𝓐𝓹 q v₁) ]
  𝓐𝓹 ap⁻¹⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹⁻¹ (Iter.q x) v₁) ]
  𝓐𝓹 (η- c) (𝟙ₚ x) = [ (1/comb ⟪ c , id⇔ ⟫) , (comb x) ]
  𝓐𝓹 (η+ c) (𝟙ₚ x) = [ (comb x) , (1/comb ⟪ c , id⇔ ⟫) ]
  𝓐𝓹 (ε+ c) [ comb x , 1/comb x₁ ] = 𝟙ₚ x
  𝓐𝓹 (ε- c) [ 1/comb x , comb x₁ ] = 𝟙ₚ x₁
  𝓐𝓹 (unite⋆l# c) [ v , v₁ ] = v₁
  𝓐𝓹 (uniti⋆l# c) v = [ (𝟙ₚ ( < (+ 1) , c , idr◎r > )) , v ]
  𝓐𝓹 (unite⋆r# c) [ v , v₁ ] = v
  𝓐𝓹 (uniti⋆r# c) v = [ v , (𝟙ₚ < + 1 , c , idr◎r >) ]

  𝓐𝓹⁻¹ : {T₁ T₂ : U} → (T₁ ⟷ T₂) → Val T₂ → Val T₁
  𝓐𝓹⁻¹ (Prim x) v = prim⁻¹ x v
  𝓐𝓹⁻¹ (c ◎ c₁) v = 𝓐𝓹⁻¹ c (𝓐𝓹⁻¹ c₁ v)
  𝓐𝓹⁻¹ (c ⊕ c₁) (inl v) = inl (𝓐𝓹⁻¹ c v)
  𝓐𝓹⁻¹ (c ⊕ c₁) (inr v) = inr (𝓐𝓹⁻¹ c₁ v)
  𝓐𝓹⁻¹ (c ⊗ c₁) [ v , w ] = [ (𝓐𝓹⁻¹ c v) , (𝓐𝓹⁻¹ c₁ w) ]
  𝓐𝓹⁻¹ foldSwap (comb < k , q , α >) = Fin2⇒1+1 (mod2 k)
  𝓐𝓹⁻¹ unfoldSwap (inl v) = comb < (+ 0) , (Prim id⟷) , id⇔ >
  𝓐𝓹⁻¹ unfoldSwap (inr v) = comb < (+ 1) , (Prim swap₊) , idr◎r >
  𝓐𝓹⁻¹ ap⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹⁻¹ (Iter.q x) v₁) ]
  𝓐𝓹⁻¹ ap⁻¹⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹 (Iter.q x) v₁) ]
  𝓐𝓹⁻¹ (η- c) [ v , comb x ] = 𝟙ₚ x
  𝓐𝓹⁻¹ (η+ c) [ comb x , v₁ ] = 𝟙ₚ x
  𝓐𝓹⁻¹ (ε+ c) (𝟙ₚ x) = [ (comb x) , (1/comb ⟪ c , id⇔ ⟫) ]
  𝓐𝓹⁻¹ (ε- c) (𝟙ₚ x) = [ (1/comb ⟪ c , id⇔ ⟫) , (comb x) ]
  𝓐𝓹⁻¹ (unite⋆l# c) v = [ 𝟙ₚ < (+ 1) , c , idr◎r > , v ]
  𝓐𝓹⁻¹ (uniti⋆l# c) [ 𝟙ₚ x , v₁ ] = v₁
  𝓐𝓹⁻¹ (unite⋆r# c) v = [ v , 𝟙ₚ < (+ 1) , c , idr◎r > ]
  𝓐𝓹⁻¹ (uniti⋆r# c) [ v , 𝟙ₚ x ] = v

swap₊-mod2 : {t : U} (k : ℤ) → (Prim (swap₊ {t} {t})) ^ k ⇔ (Prim swap₊) ^ (+ toℕ (mod2 k))
swap₊-mod2 (+_ ℕ.zero) = id⇔
swap₊-mod2 (+_ (suc ℕ.zero)) = id⇔
swap₊-mod2 (+_ (suc (suc n))) = assoc◎l ● rinv◎l ⊡ id⇔ ● idl◎l ● swap₊-mod2 (+ n)
swap₊-mod2 (-[1+_] ℕ.zero) = idr◎r
swap₊-mod2 (-[1+_] (suc ℕ.zero)) = rinv◎l
swap₊-mod2 (-[1+_] (suc (suc n))) = assoc◎l ● rinv◎l ⊡ id⇔ ● idl◎l ● swap₊-mod2 -[1+ n ]

postulate
  cong≈ : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → {v w : Val T₁} → v ≈ w → 𝓐𝓹 c v ≈ 𝓐𝓹 c w
  cong⁻¹≈ : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → {v w : Val T₂} → v ≈ w → 𝓐𝓹⁻¹ c v ≈ 𝓐𝓹⁻¹ c w

{-# TERMINATING #-}
mutual
  fwd◎bwd≈id : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : Val T₂) → (𝓐𝓹 c (𝓐𝓹⁻¹ c v)) ≈ v
  fwd◎bwd≈id (Prim x) v = refl≈ (prim◎prim⁻¹≡id x v)
  fwd◎bwd≈id (c ◎ c₁) v = trans≈ (cong≈ c₁ (fwd◎bwd≈id c (𝓐𝓹⁻¹ c₁ v))) (fwd◎bwd≈id c₁ v)
  fwd◎bwd≈id (c ⊕ c₁) (inl v) = inj₁≈ (fwd◎bwd≈id c v)
  fwd◎bwd≈id (c ⊕ c₁) (inr v) = inj₂≈ (fwd◎bwd≈id c₁ v)
  fwd◎bwd≈id (c ⊗ c₁) [ v , v₁ ] = [,]≈ (fwd◎bwd≈id c v) (fwd◎bwd≈id c₁ v₁)
  fwd◎bwd≈id (foldSwap {t}) (comb < k , q , α >) with mod2 k | swap₊-mod2 {t} k
  ... | zero | pf = #p≈ (zeroth (Prim swap₊)) < k , q , α > (idl◎l ● ⇔! (α ● pf))
  ... | suc zero | pf = #p≈ (iter (Prim swap₊)) < k , q , α > (id⇔ ⊡ (⇔! (α ● pf) ● idl◎l) ● rinv◎l) 
  ... | suc (suc ()) | _ 
  fwd◎bwd≈id unfoldSwap (inl ⋆) = refl≈ refl
  fwd◎bwd≈id unfoldSwap (inr ⋆) = refl≈ refl
  fwd◎bwd≈id ap⟷ [ comb {t} {p} < i , q , α > , v₁ ] =
    [,]≈ (#p≈ < i , q , α > < i , q , α > linv◎l)
         (fwd◎bwd≈id q v₁)
  fwd◎bwd≈id ap⁻¹⟷ [ comb x , v₁ ] = [,]≈ (refl≈ refl) (bwd◎fwd≈id (Iter.q x) v₁)
  fwd◎bwd≈id (η- c) [ 1/comb x , comb x₁ ] =
    [,]≈ (1/#p≈ x₁ (sing c) x (id⇔ ⊡ ⇔! (Sing.eq x) ● linv◎l ● linv◎r))
         (refl≈ refl)
  fwd◎bwd≈id (η+ c) [ comb x , 1/comb x₁ ] =
    [,]≈ (refl≈ refl)
         (1/#p≈ x (sing c) x₁ ((id⇔ ⊡ ⇔! (Sing.eq x₁) ● linv◎l ● linv◎r)))
  fwd◎bwd≈id (ε+ c) (𝟙ₚ x) = refl≈ refl -- trivial
    -- note that this means that we get x back on the nose.
  fwd◎bwd≈id (ε- c) (𝟙ₚ x) = refl≈ refl -- 𝟙ₚ≈ {p₁ = x} {x} x x id⇔
  fwd◎bwd≈id (unite⋆l# c) v = refl≈ refl
  fwd◎bwd≈id (uniti⋆l# c) [ 𝟙ₚ < i , q , α > , v₁ ] =
    [,]≈ (𝟙ₚ≈  < (+ 1) ℤ+ (ℤ- i) , c ◎ ! q , id⇔ ⊡ (⇔! α ● 2! (^⇔! i)) ●
                                             2! (lower (+ 1) (ℤ- i) ● idr◎l ⊡ id⇔) >
                                             (iter c) < i , q , α > id⇔)
         (refl≈ refl)
  fwd◎bwd≈id (unite⋆r# c) v = refl≈ refl
  fwd◎bwd≈id (uniti⋆r# c) [ p , 𝟙ₚ < i , q , α > ] =
   [,]≈ (refl≈ refl)
        (𝟙ₚ≈  < ℤsuc (ℤ- i) , c ◎ ! q , id⇔ ⊡ (⇔! α ● 2! (^⇔! i)) ● 2! (lower (+ 1) (ℤ- i) ● idr◎l ⊡ id⇔) > (iter c) < i , q , α > id⇔)

  bwd◎fwd≈id : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : Val T₁) → (𝓐𝓹⁻¹ c (𝓐𝓹 c v)) ≈ v
  bwd◎fwd≈id (Prim x) v = refl≈ (prim⁻¹◎prim≡id x v)
  bwd◎fwd≈id (c ◎ c₁) v = trans≈ (cong⁻¹≈ c (bwd◎fwd≈id c₁ (𝓐𝓹 c v))) (bwd◎fwd≈id c v)
  bwd◎fwd≈id (c ⊕ c₁) (inl v) = inj₁≈ (bwd◎fwd≈id c v)
  bwd◎fwd≈id (c ⊕ c₁) (inr v) = inj₂≈ (bwd◎fwd≈id c₁ v)
  bwd◎fwd≈id (c ⊗ c₁) [ v , v₁ ] = [,]≈ (bwd◎fwd≈id c v) (bwd◎fwd≈id c₁ v₁)
  bwd◎fwd≈id foldSwap (inl ⋆) = inj₁≈ ⋆≈
  bwd◎fwd≈id foldSwap (inr ⋆) = inj₂≈ ⋆≈
  bwd◎fwd≈id unfoldSwap (comb x) = {!!}
  bwd◎fwd≈id ap⟷ [ comb x , v₁ ] = [,]≈ (refl≈ refl) (bwd◎fwd≈id (Iter.q x) v₁)
  bwd◎fwd≈id ap⁻¹⟷ [ comb x , v₁ ] = {!!}
  bwd◎fwd≈id (η- c) (𝟙ₚ x) = refl≈ refl
  bwd◎fwd≈id (η+ c) (𝟙ₚ x) = refl≈ refl
  bwd◎fwd≈id (ε+ c) [ comb x , 1/comb x₁ ] = [,]≈ (refl≈ refl) (1/#p≈ x (sing c) x₁ {!!})
  bwd◎fwd≈id (ε- c) [ 1/comb x , comb x₁ ] = {!!}
  bwd◎fwd≈id (unite⋆l# c) [ 𝟙ₚ x , v₁ ] = [,]≈ (𝟙ₚ≈ {!!} {!!} x {!!}) (refl≈ refl)
  bwd◎fwd≈id (uniti⋆l# c) v = refl≈ refl
  bwd◎fwd≈id (unite⋆r# c) [ v , 𝟙ₚ x ] = {!!}
  bwd◎fwd≈id (uniti⋆r# c) v = refl≈ refl

bwd-coherence : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : Val T₂) → 𝓐𝓹⁻¹ c v ≈ 𝓐𝓹 (! c) v
bwd-coherence c v = {!!}
