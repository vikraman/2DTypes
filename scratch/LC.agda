module scratch.LC where

data Ty : Set where
  One : Ty
  _×_ _⇒_ : Ty → Ty → Ty

data Cx : Set where
  ∙ : Cx
  _,_ : Cx → Ty → Cx

variable
  Γ : Cx
  A B : Ty

data Tm : Cx → Ty → Set where
  var : Tm (Γ , A) A
  wk  : Tm Γ B → Tm (Γ , A) B
  tt  : Tm Γ One
  _,_ : Tm Γ A → Tm Γ B → Tm Γ (A × B)
  fst : Tm Γ (A × B) → Tm Γ A
  snd : Tm Γ (A × B) → Tm Γ B
  lam : Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

data Pi : Set where
  𝟘 𝟙 : Pi
  _+_ : Pi → Pi → Pi

variable
  X Y Z : Pi

data _⟷_ : Pi → Pi → Set where
  id : X ⟷ X
  _∘_ : X ⟷ Y → Y ⟷ Z → X ⟷ Z
  swap : (X + Y) ⟷ (Y + X)

R : Tm Γ (A ⇒ B) → Tm Γ (A ⇒ (A × B))
R e = lam (var , app (wk e) var)

open import Data.Product

D : Ty → Pi
D One = 𝟙
D (A × B) = D A + D B
D (A ⇒ B) = (D A + D B) + 𝟙

T : Tm ∙ (One ⇒ One) → (𝟙 ⟷ 𝟙)
T (fst e) = {!!}
T (snd e) = {!!}
T (lam e) = {!!}
T (app e₁ e₂) = {!!}
