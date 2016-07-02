{-# OPTIONS --without-K #-}

module 2D.Prim where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import 2D.Types
open import 2D.Val

------------------------------------------------------------------------------
-- evaluation of simple combinators forwards and backwards

prim : {T₁ T₂ : U} → (Prim⟷ T₁ T₂) → Val T₁ → Val T₂
prim unite₊l (inl ())
prim unite₊l (inr v) = v
prim uniti₊l v = inr v
prim unite₊r (inl v) = v
prim unite₊r (inr ())
prim uniti₊r v = inl v
prim swap₊ (inl v) = inr v
prim swap₊ (inr v) = inl v
prim assocl₊ (inl v) = inl (inl v)
prim assocl₊ (inr (inl v)) = inl (inr v)
prim assocl₊ (inr (inr v)) = inr v
prim assocr₊ (inl (inl v)) = inl v
prim assocr₊ (inl (inr v)) = inr (inl v)
prim assocr₊ (inr v) = inr (inr v)
prim unite⋆l [ v , w ] = w
prim uniti⋆l v = [ ⋆ , v ]
prim unite⋆r [ v , v₁ ] = v
prim uniti⋆r v = [ v , ⋆ ]
prim swap⋆ [ v , w ] = [ w , v ]
prim assocl⋆ [ v , [ w , z ] ] = [ [ v , w ] , z ]
prim assocr⋆ [ [ v , w ] , z ] = [ v , [ w , z ] ]
prim absorbr [ v , v₁ ] = v -- note how we pass v through, even though it's 𝟘
prim absorbl [ v , v₁ ] = v₁
prim factorzr () -- but here we can't invent values, so we have no choice
prim factorzl ()
prim dist [ inl v , w ] = inl [ v , w ]
prim dist [ inr v , w ] = inr [ v , w ]
prim factor (inl [ v , v₁ ]) = [ inl v , v₁ ]
prim factor (inr [ v , v₁ ]) = [ inr v , v₁ ]
prim distl [ v , inl v₁ ] = inl [ v , v₁ ]
prim distl [ v , inr v₁ ] = inr [ v , v₁ ]
prim factorl (inl [ v , v₁ ]) = [ v , inl v₁ ]
prim factorl (inr [ v , v₁ ]) = [ v , inr v₁ ]
prim id⟷ v = v

prim⁻¹ : {T₁ T₂ : U} → (Prim⟷ T₁ T₂) → Val T₂ → Val T₁
prim⁻¹ unite₊l v = inr v
prim⁻¹ uniti₊l (inl ())
prim⁻¹ uniti₊l (inr v) = v
prim⁻¹ unite₊r v = inl v
prim⁻¹ uniti₊r (inl v) = v
prim⁻¹ uniti₊r (inr ())
prim⁻¹ swap₊ (inl v) = inr v
prim⁻¹ swap₊ (inr v) = inl v
prim⁻¹ assocl₊ (inl (inl v)) = inl v
prim⁻¹ assocl₊ (inl (inr v)) = inr (inl v)
prim⁻¹ assocl₊ (inr v) = inr (inr v)
prim⁻¹ assocr₊ (inl v) = inl (inl v)
prim⁻¹ assocr₊ (inr (inl v)) = inl (inr v)
prim⁻¹ assocr₊ (inr (inr v)) = inr v
prim⁻¹ unite⋆l v = [ ⋆ , v ]
prim⁻¹ uniti⋆l [ v , v₁ ] = v₁
prim⁻¹ unite⋆r v = [ v , ⋆ ]
prim⁻¹ uniti⋆r [ v , v₁ ] = v
prim⁻¹ swap⋆ [ v , v₁ ] = [ v₁ , v ]
prim⁻¹ assocl⋆ [ [ v , v₁ ] , v₂ ] = [ v , [ v₁ , v₂ ] ]
prim⁻¹ assocr⋆ [ v , [ v₁ , v₂ ] ] = [ [ v , v₁ ] , v₂ ]
prim⁻¹ absorbr ()
prim⁻¹ absorbl ()
prim⁻¹ factorzr [ v , v₁ ] = v₁
prim⁻¹ factorzl [ v , v₁ ] = v
prim⁻¹ dist (inl [ v , v₁ ]) = [ inl v , v₁ ]
prim⁻¹ dist (inr [ v , v₁ ]) = [ inr v , v₁ ]
prim⁻¹ factor [ inl v , v₁ ] = inl [ v , v₁ ]
prim⁻¹ factor [ inr v , v₁ ] = inr [ v , v₁ ]
prim⁻¹ distl (inl [ v , v₁ ]) = [ v , inl v₁ ]
prim⁻¹ distl (inr [ v , v₁ ]) = [ v , inr v₁ ]
prim⁻¹ factorl [ v , inl v₁ ] = inl [ v , v₁ ]
prim⁻¹ factorl [ v , inr v₁ ] = inr [ v , v₁ ]
prim⁻¹ id⟷ v = v

prim◎prim⁻¹≡id : {T₁ T₂ : U} → (c : Prim⟷ T₁ T₂) → (v : Val T₂) → prim c (prim⁻¹ c v) ≡ v
prim◎prim⁻¹≡id unite₊l v = refl
prim◎prim⁻¹≡id uniti₊l (inl ())
prim◎prim⁻¹≡id uniti₊l (inr v) = refl
prim◎prim⁻¹≡id unite₊r v = refl
prim◎prim⁻¹≡id uniti₊r (inl v) = refl
prim◎prim⁻¹≡id uniti₊r (inr ())
prim◎prim⁻¹≡id swap₊ (inl v) = refl
prim◎prim⁻¹≡id swap₊ (inr v) = refl
prim◎prim⁻¹≡id assocl₊ (inl (inl v)) = refl
prim◎prim⁻¹≡id assocl₊ (inl (inr v)) = refl
prim◎prim⁻¹≡id assocl₊ (inr v) = refl
prim◎prim⁻¹≡id assocr₊ (inl v) = refl
prim◎prim⁻¹≡id assocr₊ (inr (inl v)) = refl
prim◎prim⁻¹≡id assocr₊ (inr (inr v)) = refl
prim◎prim⁻¹≡id unite⋆l v = refl
prim◎prim⁻¹≡id uniti⋆l [ ⋆ , v₁ ] = refl
prim◎prim⁻¹≡id unite⋆r v = refl
prim◎prim⁻¹≡id uniti⋆r [ v , ⋆ ] = refl
prim◎prim⁻¹≡id swap⋆ [ v , v₁ ] = refl
prim◎prim⁻¹≡id assocl⋆ [ [ v , v₁ ] , v₂ ] = refl
prim◎prim⁻¹≡id assocr⋆ [ v , [ v₁ , v₂ ] ] = refl
prim◎prim⁻¹≡id absorbl ()
prim◎prim⁻¹≡id absorbr ()
prim◎prim⁻¹≡id factorzr [ v , () ]
prim◎prim⁻¹≡id factorzl [ () , v₁ ]
prim◎prim⁻¹≡id dist (inl [ v , v₁ ]) = refl
prim◎prim⁻¹≡id dist (inr [ v , v₁ ]) = refl
prim◎prim⁻¹≡id factor [ inl v , v₁ ] = refl
prim◎prim⁻¹≡id factor [ inr v , v₁ ] = refl
prim◎prim⁻¹≡id distl (inl [ v , v₁ ]) = refl
prim◎prim⁻¹≡id distl (inr [ v , v₁ ]) = refl
prim◎prim⁻¹≡id factorl [ v , inl v₁ ] = refl
prim◎prim⁻¹≡id factorl [ v , inr v₁ ] = refl
prim◎prim⁻¹≡id id⟷ v = refl

prim⁻¹◎prim≡id : {T₁ T₂ : U} → (c : Prim⟷ T₁ T₂) → (v : Val T₁) → prim⁻¹ c (prim c v) ≡ v
prim⁻¹◎prim≡id unite₊l (inl ())
prim⁻¹◎prim≡id unite₊l (inr v) = refl
prim⁻¹◎prim≡id uniti₊l v = refl
prim⁻¹◎prim≡id unite₊r (inl v) = refl
prim⁻¹◎prim≡id unite₊r (inr ())
prim⁻¹◎prim≡id uniti₊r v = refl
prim⁻¹◎prim≡id swap₊ (inl v) = refl
prim⁻¹◎prim≡id swap₊ (inr v) = refl
prim⁻¹◎prim≡id assocl₊ (inl v) = refl
prim⁻¹◎prim≡id assocl₊ (inr (inl v)) = refl
prim⁻¹◎prim≡id assocl₊ (inr (inr v)) = refl
prim⁻¹◎prim≡id assocr₊ (inl (inl v)) = refl
prim⁻¹◎prim≡id assocr₊ (inl (inr v)) = refl
prim⁻¹◎prim≡id assocr₊ (inr v) = refl
prim⁻¹◎prim≡id unite⋆l [ ⋆ , v₁ ] = refl
prim⁻¹◎prim≡id uniti⋆l v = refl
prim⁻¹◎prim≡id unite⋆r [ v , ⋆ ] = refl
prim⁻¹◎prim≡id uniti⋆r v = refl
prim⁻¹◎prim≡id swap⋆ [ v , v₁ ] = refl
prim⁻¹◎prim≡id assocl⋆ [ v , [ v₁ , v₂ ] ] = refl
prim⁻¹◎prim≡id assocr⋆ [ [ v , v₁ ] , v₂ ] = refl
prim⁻¹◎prim≡id absorbr [ () , v₁ ]
prim⁻¹◎prim≡id absorbl [ v , () ]
prim⁻¹◎prim≡id factorzr ()
prim⁻¹◎prim≡id factorzl ()
prim⁻¹◎prim≡id dist [ inl v , v₁ ] = refl
prim⁻¹◎prim≡id dist [ inr v , v₁ ] = refl
prim⁻¹◎prim≡id factor (inl [ v , v₁ ]) = refl
prim⁻¹◎prim≡id factor (inr [ v , v₁ ]) = refl
prim⁻¹◎prim≡id distl [ v , inl v₁ ] = refl
prim⁻¹◎prim≡id distl [ v , inr v₁ ] = refl
prim⁻¹◎prim≡id factorl (inl [ v , v₁ ]) = refl
prim⁻¹◎prim≡id factorl (inr [ v , v₁ ]) = refl
prim⁻¹◎prim≡id id⟷ v = refl

prim-cong≈ : {T₁ T₂ : U} → (c : Prim⟷ T₁ T₂) → {v w : Val T₁} → v ≈ w → prim c v ≈ prim c w
prim-cong≈ c ⋆≈ = refl≈ refl
prim-cong≈ uniti₊l (#p≈ p^i p^j x) = inj₂≈ (#p≈ p^i p^j x)
prim-cong≈ uniti₊r (#p≈ p^i p^j x) = inj₁≈ (#p≈ p^i p^j x)
prim-cong≈ uniti⋆l (#p≈ p^i p^j x) = [,]≈ ⋆≈ (#p≈ p^i p^j x)
prim-cong≈ uniti⋆r (#p≈ p^i p^j x) = [,]≈ (#p≈ p^i p^j x) ⋆≈
prim-cong≈ id⟷ (#p≈ p^i p^j x) = #p≈ p^i p^j x
prim-cong≈ uniti₊l (1/#p≈ q p₁ p₂ x) = inj₂≈ (1/#p≈ q p₁ p₂ x)
prim-cong≈ uniti₊r (1/#p≈ q p₁ p₂ x) = inj₁≈ (1/#p≈ q p₁ p₂ x)
prim-cong≈ uniti⋆l (1/#p≈ q p₁ p₂ x) = [,]≈ ⋆≈ (1/#p≈ q p₁ p₂ x)
prim-cong≈ uniti⋆r (1/#p≈ q p₁ p₂ x) = [,]≈ (1/#p≈ q p₁ p₂ x) ⋆≈
prim-cong≈ id⟷ (1/#p≈ q p₁ p₂ x) = 1/#p≈ q p₁ p₂ x
prim-cong≈ uniti₊l (𝟙ₚ≈ p₁ q r x) = inj₂≈ (𝟙ₚ≈ p₁ q r x)
prim-cong≈ uniti₊r (𝟙ₚ≈ p₁ q r x) = inj₁≈ (𝟙ₚ≈ p₁ q r x)
prim-cong≈ uniti⋆l (𝟙ₚ≈ p₁ q r x) = [,]≈ ⋆≈ (𝟙ₚ≈ p₁ q r x)
prim-cong≈ uniti⋆r (𝟙ₚ≈ p₁ q r x) = [,]≈ (𝟙ₚ≈ p₁ q r x) ⋆≈
prim-cong≈ id⟷ (𝟙ₚ≈ p₁ q r x) = 𝟙ₚ≈ p₁ q r x
prim-cong≈ uniti₊l ([,]≈ p q) = inj₂≈ ([,]≈ p q)
prim-cong≈ uniti₊r ([,]≈ p q) = inj₁≈ ([,]≈ p q)
prim-cong≈ unite⋆l ([,]≈ p q) = q
prim-cong≈ uniti⋆l ([,]≈ p q) = [,]≈ ⋆≈ ([,]≈ p q)
prim-cong≈ unite⋆r ([,]≈ p q) = p
prim-cong≈ uniti⋆r ([,]≈ p q) = [,]≈ ([,]≈ p q) ⋆≈
prim-cong≈ swap⋆ ([,]≈ p q) = [,]≈ q p
prim-cong≈ assocl⋆ ([,]≈ p ([,]≈ x x₁)) = [,]≈ ([,]≈ p x) x₁
prim-cong≈ assocr⋆ ([,]≈ ([,]≈ x x₁) q) = [,]≈ x ([,]≈ x₁ q)
prim-cong≈ absorbr ([,]≈ p q) = p
prim-cong≈ absorbl ([,]≈ p q) = q
prim-cong≈ dist ([,]≈ (inj₁≈ x) q) = inj₁≈ ([,]≈ x q)
prim-cong≈ dist ([,]≈ (inj₂≈ x) q) = inj₂≈ ([,]≈ x q)
prim-cong≈ distl ([,]≈ p (inj₁≈ x)) = inj₁≈ ([,]≈ p x)
prim-cong≈ distl ([,]≈ p (inj₂≈ x)) = inj₂≈ ([,]≈ p x)
prim-cong≈ id⟷ ([,]≈ p q) = [,]≈ p q
prim-cong≈ unite₊l (inj₁≈ {_} {_} {} p)
prim-cong≈ uniti₊l (inj₁≈ p) = inj₂≈ (inj₁≈ p)
prim-cong≈ unite₊r (inj₁≈ p) = p
prim-cong≈ uniti₊r (inj₁≈ p) = inj₁≈ (inj₁≈ p)
prim-cong≈ swap₊ (inj₁≈ p) = inj₂≈ p
prim-cong≈ assocl₊ (inj₁≈ p) = inj₁≈ (inj₁≈ p)
prim-cong≈ assocr₊ (inj₁≈ (inj₁≈ x)) = inj₁≈ x
prim-cong≈ assocr₊ (inj₁≈ (inj₂≈ x)) = inj₂≈ (inj₁≈ x)
prim-cong≈ uniti⋆l (inj₁≈ p) = [,]≈ ⋆≈ (inj₁≈ p)
prim-cong≈ uniti⋆r (inj₁≈ p) = [,]≈ (inj₁≈ p) ⋆≈
prim-cong≈ factor (inj₁≈ ([,]≈ x x₁)) = [,]≈ (inj₁≈ x) x₁
prim-cong≈ factorl (inj₁≈ ([,]≈ x x₁)) = [,]≈ x (inj₁≈ x₁)
prim-cong≈ id⟷ (inj₁≈ p) = inj₁≈ p
prim-cong≈ unite₊l (inj₂≈ p) = p
prim-cong≈ uniti₊l (inj₂≈ p) = inj₂≈ (inj₂≈ p)
prim-cong≈ unite₊r (inj₂≈ {_} {_} {} p)
prim-cong≈ uniti₊r (inj₂≈ p) = inj₁≈ (inj₂≈ p)
prim-cong≈ swap₊ (inj₂≈ p) = inj₁≈ p
prim-cong≈ assocl₊ (inj₂≈ (inj₁≈ x)) = inj₁≈ (inj₂≈ x)
prim-cong≈ assocl₊ (inj₂≈ (inj₂≈ x)) = inj₂≈ x
prim-cong≈ assocr₊ (inj₂≈ p) = inj₂≈ (inj₂≈ p)
prim-cong≈ uniti⋆l (inj₂≈ p) = [,]≈ ⋆≈ (inj₂≈ p)
prim-cong≈ uniti⋆r (inj₂≈ p) = [,]≈ (inj₂≈ p) ⋆≈
prim-cong≈ factor (inj₂≈ ([,]≈ x x₁)) = [,]≈ (inj₂≈ x) x₁
prim-cong≈ factorl (inj₂≈ ([,]≈ x x₁)) = [,]≈ x (inj₂≈ x₁)
prim-cong≈ id⟷ (inj₂≈ p) = inj₂≈ p
