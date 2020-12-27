{-# OPTIONS --without-K #-}

module Pi+.Swap where

data U : Set where
  O : U
  I+_ : U → U

infixr 40 I+_
infix 30 _⟷₁_
infixr 50 _◎_ ⊕_

-- data _⟷₁_  : U → U → Set where
--     swap₊ : {t : U} → I+ (I+ t) ⟷₁ I+ (I+ t)
--     id⟷₁  : {t : U} → t ⟷₁ t
--     _◎_   : {t : U} → (t ⟷₁ t) → (t ⟷₁ t) → (t ⟷₁ t)
--     ⊕_    : {t : U} → (t ⟷₁ t) → (I+ t⟷₁ I+ t)

data _⟷₁_  : U → U → Set where
    swap₊ : {t : U} → I+ (I+ t) ⟷₁ I+ (I+ t)
    id⟷₁  : {t : U} → t ⟷₁ t
    !⟷₁   : {t₁ t₂ : U} → t₁ ⟷₁ t₂ → t₂ ⟷₁ t₁
    _◎_   : {t₁ t₂ t₃ : U} → (t₁ ⟷₁ t₂) → (t₂ ⟷₁ t₃) → (t₁ ⟷₁ t₃)
    ⊕_    : {t₁ t₂ : U} → (t₁ ⟷₁ t₂) → (I+ t₁ ⟷₁ I+ t₂)

--   unite₊l : {t : U} → O + t ⟷₁ t
--   swap₊   : {t₁ t₂ : U} → t₁ + t₂ ⟷₁ t₂ + t₁
--   assocl₊ : {t₁ t₂ t₃ : U} → t₁ + (t₂ + t₃) ⟷₁ (t₁ + t₂) + t₃
--   _⊕_     : {t₁ t₂ t₃ t₄ : U} → (t₁ ⟷₁ t₃) → (t₂ ⟷₁ t₄) → (t₁ + t₂ ⟷₁ t₃ + t₄)

data _⟷₂_ : {X Y : U} → X ⟷₁ Y → X ⟷₁ Y → Set where
    swap₊² : {t : U} → swap₊ {t} ◎ swap₊ {t} ⟷₂ id⟷₁
    -- hexagon
    -- functoriality/naturality
    -- groupoid laws

import Pi+.Syntax as P
open import Pi+.Level0
open import lib.Base
open import lib.types.Nat

fin : ℕ → U
fin O = O
fin (S n) = I+ fin n

flatten : P.U → U
flatten X = fin (∣ X ∣)

inject : U → P.U
inject O = P.O
inject (I+ X) = P.I P.+ inject X

canon : P.U → P.U
canon X = inject (flatten X)

inject-fin-+ : (m n : ℕ) → inject (fin m) P.+ inject (fin n) P.⟷₁ inject (fin (m + n))
inject-fin-+ O n = P.unite₊l
inject-fin-+ (S m) n = P.assocr₊ P.◎ P.id⟷₁ P.⊕ inject-fin-+ m n

norm : (t : P.U) → t P.⟷₁ canon t 
norm P.O = P.id⟷₁
norm P.I = P.!⟷₁ (P.swap₊ P.◎ P.unite₊l)
norm (X P.+ Y) = (norm X P.⊕ norm Y) P.◎ inject-fin-+ ∣ X ∣ ∣ Y ∣

flatten₁ : (X Y : P.U) → X P.⟷₁ Y → (flatten X) ⟷₁ (flatten Y)
flatten₁ .(P.O P.+ Y) Y P.unite₊l = id⟷₁
flatten₁ .(_ P.+ _) .(_ P.+ _) P.swap₊ = {!   !}
flatten₁ .(_ P.+ _ P.+ _) .((_ P.+ _) P.+ _) P.assocl₊ = {!   !}
flatten₁ X .X P.id⟷₁ = {!   !}
flatten₁ X Y (P.!⟷₁ c) = {!   !}
flatten₁ X Y (c P.◎ c₁) = {!   !}
flatten₁ .(_ P.+ _) .(_ P.+ _) (c P.⊕ c₁) = {!   !}
