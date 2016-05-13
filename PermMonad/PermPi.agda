{-# OPTIONS --without-K #-}

module PermPi where
open import Level renaming (zero to lzero; suc to lsuc) 
open import Algebra
open import Algebra.Structures
import Algebra.FunctionProperties
open import Data.Empty
open import Data.Unit hiding (_≤_; _≤?_)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_+_ to _ℤ+_)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Fin using (Fin; zero; suc; inject+; raise; inject≤; toℕ; fromℕ)
  renaming (_+_ to _F+_)
open import Data.Fin.Properties hiding (reverse)
open import Data.Sum hiding (map)
open import Data.Bool
open import Data.Product hiding (map)
open import Data.Vec hiding (reverse)
open import Data.Nat hiding (_⊔_)
open import Data.Integer using (+_) 
open import Relation.Nullary
import Relation.Binary.PropositionalEquality as P
open P.≡-Reasoning
open import Categories.Category
open import Categories.Groupoid
open import Relation.Binary.Core using (Rel; IsEquivalence)

open import Level
open import Categories.Category 
import Categories.Morphisms
open import Relation.Binary
  using (Rel; IsEquivalence; module IsEquivalence; Reflexive; Symmetric; Transitive)
  renaming (_⇒_ to _⊆_)
open import Function using (flip)
open import Categories.Support.PropositionalEquality
open import Categories.Support.Equivalence
open import Categories.Support.EqReasoning
open import Data.Product
open import Categories.Groupoid
open import Categories.Discrete
open import Categories.Monad
open import Relation.Binary.PropositionalEquality
open Algebra.FunctionProperties (P._≡_ {A = ℤ})

data U : Set where
  ZERO   : U
  ONE    : U
  PLUS   : U → U → U
  TIMES  : U → U → U

⟦_⟧ : U → Set
⟦ ZERO ⟧         = ⊥ 
⟦ ONE ⟧          = ⊤
⟦ PLUS t₁ t₂ ⟧   = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧  = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

∣_∣ : U → ℕ
∣ ZERO ∣         = 0
∣ ONE ∣          = 1
∣ PLUS t₁ t₂ ∣   = ∣ t₁ ∣ + ∣ t₂ ∣
∣ TIMES t₁ t₂ ∣  = ∣ t₁ ∣ * ∣ t₂ ∣

infix  30 _⟷_
infixr 50 _◎_

data _⟷_ : U → U → Set where
  unite₊l : {t : U} → PLUS ZERO t ⟷ t
  uniti₊l : {t : U} → t ⟷ PLUS ZERO t
  unite₊r : {t : U} → PLUS t ZERO ⟷ t
  uniti₊r : {t : U} → t ⟷ PLUS t ZERO
  swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆l  : {t : U} → TIMES ONE t ⟷ t
  uniti⋆l  : {t : U} → t ⟷ TIMES ONE t
  unite⋆r : {t : U} → TIMES t ONE ⟷ t
  uniti⋆r : {t : U} → t ⟷ TIMES t ONE
  swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  absorbr : {t : U} → TIMES ZERO t ⟷ ZERO
  absorbl : {t : U} → TIMES t ZERO ⟷ ZERO
  factorzr : {t : U} → ZERO ⟷ TIMES t ZERO
  factorzl : {t : U} → ZERO ⟷ TIMES ZERO t
  dist    : {t₁ t₂ t₃ : U} → 
            TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)
  factor  : {t₁ t₂ t₃ : U} → 
            PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  distl   : {t₁ t₂ t₃ : U } →
            TIMES t₁ (PLUS t₂ t₃) ⟷ PLUS (TIMES t₁ t₂) (TIMES t₁ t₃)
  factorl : {t₁ t₂ t₃ : U } →
            PLUS (TIMES t₁ t₂) (TIMES t₁ t₃) ⟷ TIMES t₁ (PLUS t₂ t₃)
  id⟷    : {t : U} → t ⟷ t
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} → 
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : U} → 
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)

! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
! unite₊l   = uniti₊l
! uniti₊l   = unite₊l
! unite₊r   = uniti₊r
! uniti₊r   = unite₊r
! swap₊     = swap₊
! assocl₊   = assocr₊
! assocr₊   = assocl₊
! unite⋆l   = uniti⋆l
! uniti⋆l   = unite⋆l
! unite⋆r   = uniti⋆r
! uniti⋆r   = unite⋆r
! swap⋆     = swap⋆
! assocl⋆   = assocr⋆
! assocr⋆   = assocl⋆
! absorbl   = factorzr
! absorbr   = factorzl
! factorzl  = absorbr
! factorzr  = absorbl
! dist      = factor 
! factor    = dist
! distl     = factorl
! factorl   = distl
! id⟷       = id⟷
! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁ 
! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
! (c₁ ⊗ c₂) = (! c₁) ⊗ (! c₂)

infix  30 _⇔_

data _⇔_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  assoc◎l : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
          (c₁ ◎ (c₂ ◎ c₃)) ⇔ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
          ((c₁ ◎ c₂) ◎ c₃) ⇔ (c₁ ◎ (c₂ ◎ c₃))
  assocl⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊) ⇔ (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃))
  assocl⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃)) ⇔ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊)
  assocl⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆) ⇔ (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃))
  assocl⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃)) ⇔ ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆)
  assocr⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⇔ (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃)))
  assocr⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
           (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃))) ⇔ (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆)
  assocr⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆) ⇔ (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃)))
  assocr⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
           (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))) ⇔ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
  dist⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
      ((a ⊕ b) ⊗ c) ◎ dist ⇔ dist ◎ ((a ⊗ c) ⊕ (b ⊗ c))
  dist⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
      dist ◎ ((a ⊗ c) ⊕ (b ⊗ c)) ⇔ ((a ⊕ b) ⊗ c) ◎ dist
  distl⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
      (a ⊗ (b ⊕ c)) ◎ distl ⇔ distl ◎ ((a ⊗ b) ⊕ (a ⊗ c))
  distl⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
      distl ◎ ((a ⊗ b) ⊕ (a ⊗ c)) ⇔ (a ⊗ (b ⊕ c)) ◎ distl
  factor⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
       ((a ⊗ c) ⊕ (b ⊗ c)) ◎ factor ⇔ factor ◎ ((a ⊕ b) ⊗ c)
  factor⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
       factor ◎ ((a ⊕ b) ⊗ c) ⇔ ((a ⊗ c) ⊕ (b ⊗ c)) ◎ factor
  factorl⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
       ((a ⊗ b) ⊕ (a ⊗ c)) ◎ factorl ⇔ factorl ◎ (a ⊗ (b ⊕ c))
  factorl⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
       factorl ◎ (a ⊗ (b ⊕ c)) ⇔ ((a ⊗ b) ⊕ (a ⊗ c)) ◎ factorl
  idl◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (id⟷ ◎ c) ⇔ c
  idl◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ id⟷ ◎ c
  idr◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ id⟷) ⇔ c
  idr◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ (c ◎ id⟷) 
  linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ ! c) ⇔ id⟷
  linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (c ◎ ! c) 
  rinv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (! c ◎ c) ⇔ id⟷
  rinv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (! c ◎ c) 
  unite₊l⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (unite₊l ◎ c₂) ⇔ ((c₁ ⊕ c₂) ◎ unite₊l)
  unite₊l⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          ((c₁ ⊕ c₂) ◎ unite₊l) ⇔ (unite₊l ◎ c₂)
  uniti₊l⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (uniti₊l ◎ (c₁ ⊕ c₂)) ⇔ (c₂ ◎ uniti₊l)
  uniti₊l⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (c₂ ◎ uniti₊l) ⇔ (uniti₊l ◎ (c₁ ⊕ c₂))
  unite₊r⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (unite₊r ◎ c₂) ⇔ ((c₂ ⊕ c₁) ◎ unite₊r)
  unite₊r⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          ((c₂ ⊕ c₁) ◎ unite₊r) ⇔ (unite₊r ◎ c₂)
  uniti₊r⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (uniti₊r ◎ (c₂ ⊕ c₁)) ⇔ (c₂ ◎ uniti₊r)
  uniti₊r⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (c₂ ◎ uniti₊r) ⇔ (uniti₊r ◎ (c₂ ⊕ c₁))
  swapl₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          (swap₊ ◎ (c₁ ⊕ c₂)) ⇔ ((c₂ ⊕ c₁) ◎ swap₊)
  swapr₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          ((c₂ ⊕ c₁) ◎ swap₊) ⇔ (swap₊ ◎ (c₁ ⊕ c₂))
  unitel⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (unite⋆l ◎ c₂) ⇔ ((c₁ ⊗ c₂) ◎ unite⋆l)
  uniter⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          ((c₁ ⊗ c₂) ◎ unite⋆l) ⇔ (unite⋆l ◎ c₂)
  unitil⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (uniti⋆l ◎ (c₁ ⊗ c₂)) ⇔ (c₂ ◎ uniti⋆l)
  unitir⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (c₂ ◎ uniti⋆l) ⇔ (uniti⋆l ◎ (c₁ ⊗ c₂))
  unitel⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (unite⋆r ◎ c₂) ⇔ ((c₂ ⊗ c₁) ◎ unite⋆r)
  uniter⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          ((c₂ ⊗ c₁) ◎ unite⋆r) ⇔ (unite⋆r ◎ c₂)
  unitil⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (uniti⋆r ◎ (c₂ ⊗ c₁)) ⇔ (c₂ ◎ uniti⋆r)
  unitir⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (c₂ ◎ uniti⋆r) ⇔ (uniti⋆r ◎ (c₂ ⊗ c₁))
  swapl⋆⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          (swap⋆ ◎ (c₁ ⊗ c₂)) ⇔ ((c₂ ⊗ c₁) ◎ swap⋆)
  swapr⋆⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          ((c₂ ⊗ c₁) ◎ swap⋆) ⇔ (swap⋆ ◎ (c₁ ⊗ c₂))
  id⇔     : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ c
  trans⇔  : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} → 
         (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊡_  : {t₁ t₂ t₃ : U} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₁ ⟷ t₂} {c₄ : t₂ ⟷ t₃} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {t₁ t₂ t₃ t₄ : U} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  resp⊗⇔  : {t₁ t₂ t₃ t₄ : U} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊗ c₂) ⇔ (c₃ ⊗ c₄)
  -- below are the combinators added for the RigCategory structure
  id⟷⊕id⟷⇔ : {t₁ t₂ : U} → (id⟷ {t₁} ⊕ id⟷ {t₂}) ⇔ id⟷
  split⊕-id⟷ : {t₁ t₂ : U} → (id⟷ {PLUS t₁ t₂}) ⇔ (id⟷ ⊕ id⟷)
  hom⊕◎⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⇔ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⇔ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
  id⟷⊗id⟷⇔ : {t₁ t₂ : U} → (id⟷ {t₁} ⊗ id⟷ {t₂}) ⇔ id⟷
  split⊗-id⟷ : {t₁ t₂ : U} → (id⟷ {TIMES t₁ t₂}) ⇔ (id⟷ ⊗ id⟷)
  hom⊗◎⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄)) ⇔ ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄))
  hom◎⊗⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
         ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄)) ⇔ ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄))
  -- associativity triangle
  triangle⊕l : {t₁ t₂ : U} →
    (unite₊r {t₁} ⊕ id⟷ {t₂}) ⇔ assocr₊ ◎ (id⟷ ⊕ unite₊l)
  triangle⊕r : {t₁ t₂ : U} →
    assocr₊ ◎ (id⟷ {t₁} ⊕ unite₊l {t₂}) ⇔ (unite₊r ⊕ id⟷)
  triangle⊗l : {t₁ t₂ : U} →
    ((unite⋆r {t₁}) ⊗ id⟷ {t₂}) ⇔ assocr⋆ ◎ (id⟷ ⊗ unite⋆l)
  triangle⊗r : {t₁ t₂ : U} →
    (assocr⋆ ◎ (id⟷ {t₁} ⊗ unite⋆l {t₂})) ⇔ (unite⋆r ⊗ id⟷)
  pentagon⊕l : {t₁ t₂ t₃ t₄ : U} →
    assocr₊ ◎ (assocr₊ {t₁} {t₂} {PLUS t₃ t₄}) ⇔
    ((assocr₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊)
  pentagon⊕r : {t₁ t₂ t₃ t₄ : U} →
    ((assocr₊ {t₁} {t₂} {t₃} ⊕ id⟷ {t₄}) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊) ⇔
    assocr₊ ◎ assocr₊
  pentagon⊗l : {t₁ t₂ t₃ t₄ : U} →
    assocr⋆ ◎ (assocr⋆ {t₁} {t₂} {TIMES t₃ t₄}) ⇔
    ((assocr⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆)
  pentagon⊗r : {t₁ t₂ t₃ t₄ : U} →
    ((assocr⋆ {t₁} {t₂} {t₃} ⊗ id⟷ {t₄}) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆) ⇔ 
    assocr⋆ ◎ assocr⋆
  -- from the braiding
  -- unit coherence
  unite₊l-coh-l : {t₁ : U} → unite₊l {t₁} ⇔ swap₊ ◎ unite₊r
  unite₊l-coh-r : {t₁ : U} → swap₊ ◎ unite₊r ⇔ unite₊l {t₁}
  unite⋆l-coh-l : {t₁ : U} → unite⋆l {t₁} ⇔ swap⋆ ◎ unite⋆r
  unite⋆l-coh-r : {t₁ : U} → swap⋆ ◎ unite⋆r ⇔ unite⋆l {t₁}
  hexagonr⊕l : {t₁ t₂ t₃ : U} →
    (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃} ⇔
    ((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊)
  hexagonr⊕r : {t₁ t₂ t₃ : U} →
    ((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊) ⇔
    (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃}
  hexagonl⊕l : {t₁ t₂ t₃ : U} →
    (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃} ⇔
    ((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷)
  hexagonl⊕r : {t₁ t₂ t₃ : U} →
    ((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷) ⇔
    (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃}
  hexagonr⊗l : {t₁ t₂ t₃ : U} →
    (assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃} ⇔
    ((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆)
  hexagonr⊗r : {t₁ t₂ t₃ : U} →
    ((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆) ⇔
    (assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃}
  hexagonl⊗l : {t₁ t₂ t₃ : U} →
    (assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃} ⇔
    ((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷)
  hexagonl⊗r : {t₁ t₂ t₃ : U} →
    ((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷) ⇔
    (assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃}
  absorbl⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    (c₁ ⊗ id⟷ {ZERO}) ◎ absorbl ⇔ absorbl ◎ id⟷ {ZERO}
  absorbl⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    absorbl ◎ id⟷ {ZERO} ⇔ (c₁ ⊗ id⟷ {ZERO}) ◎ absorbl
  absorbr⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    (id⟷ {ZERO} ⊗ c₁) ◎ absorbr ⇔ absorbr ◎ id⟷ {ZERO}
  absorbr⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    absorbr ◎ id⟷ {ZERO} ⇔ (id⟷ {ZERO} ⊗ c₁) ◎ absorbr
  factorzl⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    id⟷ ◎ factorzl ⇔ factorzl ◎ (id⟷ ⊗ c₁)
  factorzl⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    factorzl ◎ (id⟷ {ZERO} ⊗ c₁) ⇔ id⟷ {ZERO} ◎ factorzl
  factorzr⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    id⟷ ◎ factorzr ⇔ factorzr ◎ (c₁ ⊗ id⟷)
  factorzr⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    factorzr ◎ (c₁ ⊗ id⟷) ⇔ id⟷ ◎ factorzr
  -- from the coherence conditions of RigCategory
  swap₊distl⇔l : {t₁ t₂ t₃ : U} →
    (id⟷ {t₁} ⊗ swap₊ {t₂} {t₃}) ◎ distl ⇔ distl ◎ swap₊
  swap₊distl⇔r : {t₁ t₂ t₃ : U} →
    distl ◎ swap₊ ⇔ (id⟷ {t₁} ⊗ swap₊ {t₂} {t₃}) ◎ distl
  dist-swap⋆⇔l : {t₁ t₂ t₃ : U} →
    dist {t₁} {t₂} {t₃} ◎ (swap⋆ ⊕ swap⋆) ⇔ swap⋆ ◎ distl
  dist-swap⋆⇔r : {t₁ t₂ t₃ : U} →
    swap⋆ ◎ distl {t₁} {t₂} {t₃} ⇔ dist ◎ (swap⋆ ⊕ swap⋆)
  assocl₊-dist-dist⇔l : {t₁ t₂ t₃ t₄ : U} →
    ((assocl₊ {t₁} {t₂} {t₃} ⊗ id⟷ {t₄}) ◎ dist) ◎ (dist ⊕ id⟷) ⇔
    (dist ◎ (id⟷ ⊕ dist)) ◎ assocl₊
  assocl₊-dist-dist⇔r : {t₁ t₂ t₃ t₄ : U} →
    (dist {t₁} ◎ (id⟷ ⊕ dist {t₂} {t₃} {t₄})) ◎ assocl₊ ⇔
    ((assocl₊ ⊗ id⟷) ◎ dist) ◎ (dist ⊕ id⟷)
  assocl⋆-distl⇔l : {t₁ t₂ t₃ t₄ : U} →
    assocl⋆ {t₁} {t₂} ◎ distl {TIMES t₁ t₂} {t₃} {t₄} ⇔
    ((id⟷ ⊗ distl) ◎ distl) ◎ (assocl⋆ ⊕ assocl⋆)
  assocl⋆-distl⇔r : {t₁ t₂ t₃ t₄ : U} →
    ((id⟷ ⊗ distl) ◎ distl) ◎ (assocl⋆ ⊕ assocl⋆) ⇔
    assocl⋆ {t₁} {t₂} ◎ distl {TIMES t₁ t₂} {t₃} {t₄}  
  absorbr0-absorbl0⇔ : absorbr {ZERO} ⇔ absorbl {ZERO}
  absorbl0-absorbr0⇔ : absorbl {ZERO} ⇔ absorbr {ZERO}
  absorbr⇔distl-absorb-unite : {t₁ t₂ : U} →
    absorbr ⇔ (distl {t₂ = t₁} {t₂} ◎ (absorbr ⊕ absorbr)) ◎ unite₊l
  distl-absorb-unite⇔absorbr : {t₁ t₂ : U} →
    (distl {t₂ = t₁} {t₂} ◎ (absorbr ⊕ absorbr)) ◎ unite₊l ⇔ absorbr
  unite⋆r0-absorbr1⇔ : unite⋆r ⇔ absorbr
  absorbr1-unite⋆r-⇔ : absorbr ⇔ unite⋆r
  absorbl≡swap⋆◎absorbr : {t₁ : U} → absorbl {t₁} ⇔ swap⋆ ◎ absorbr
  swap⋆◎absorbr≡absorbl : {t₁ : U} → swap⋆ ◎ absorbr ⇔ absorbl {t₁}
  absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr : {t₁ t₂ : U} →
    absorbr ⇔ (assocl⋆ {ZERO} {t₁} {t₂} ◎ (absorbr ⊗ id⟷)) ◎ absorbr
  [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr : {t₁ t₂ : U} →
    (assocl⋆ {ZERO} {t₁} {t₂} ◎ (absorbr ⊗ id⟷)) ◎ absorbr ⇔ absorbr
  [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr : {t₁ t₂ : U} →
    (id⟷ ⊗ absorbr {t₂}) ◎ absorbl {t₁} ⇔
    (assocl⋆ ◎ (absorbl ⊗ id⟷)) ◎ absorbr
  assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl : {t₁ t₂ : U} →
    (assocl⋆ ◎ (absorbl ⊗ id⟷)) ◎ absorbr ⇔
    (id⟷ ⊗ absorbr {t₂}) ◎ absorbl {t₁}
  elim⊥-A[0⊕B]⇔l : {t₁ t₂ : U} →
     (id⟷ {t₁} ⊗ unite₊l {t₂}) ⇔
     (distl ◎ (absorbl ⊕ id⟷)) ◎ unite₊l
  elim⊥-A[0⊕B]⇔r : {t₁ t₂ : U} →
     (distl ◎ (absorbl ⊕ id⟷)) ◎ unite₊l ⇔ (id⟷ {t₁} ⊗ unite₊l {t₂})
  elim⊥-1[A⊕B]⇔l : {t₁ t₂ : U} →
    unite⋆l ⇔ 
    distl ◎ (unite⋆l {t₁} ⊕ unite⋆l {t₂})
  elim⊥-1[A⊕B]⇔r : {t₁ t₂ : U} →
    distl ◎ (unite⋆l {t₁} ⊕ unite⋆l {t₂}) ⇔ unite⋆l
  fully-distribute⇔l : {t₁ t₂ t₃ t₄ : U} → 
    (distl ◎ (dist {t₁} {t₂} {t₃} ⊕ dist {t₁} {t₂} {t₄})) ◎ assocl₊ ⇔
      ((((dist ◎ (distl ⊕ distl)) ◎ assocl₊) ◎ (assocr₊ ⊕ id⟷)) ◎
         ((id⟷ ⊕ swap₊) ⊕ id⟷)) ◎ (assocl₊ ⊕ id⟷)
  fully-distribute⇔r : {t₁ t₂ t₃ t₄ : U} →
    ((((dist ◎ (distl ⊕ distl)) ◎ assocl₊) ◎ (assocr₊ ⊕ id⟷)) ◎
       ((id⟷ ⊕ swap₊) ⊕ id⟷)) ◎ (assocl₊ ⊕ id⟷) ⇔
    (distl ◎ (dist {t₁} {t₂} {t₃} ⊕ dist {t₁} {t₂} {t₄})) ◎ assocl₊

2! : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
2! assoc◎l = assoc◎r
2! assoc◎r = assoc◎l
2! assocl⊕l = assocl⊕r
2! assocl⊕r = assocl⊕l
2! assocl⊗l = assocl⊗r
2! assocl⊗r = assocl⊗l
2! assocr⊕r = assocr⊕l
2! assocr⊕l = assocr⊕r
2! assocr⊗r = assocr⊗l
2! assocr⊗l = assocr⊗r
2! dist⇔l = dist⇔r
2! dist⇔r = dist⇔l
2! distl⇔l = distl⇔r
2! distl⇔r = distl⇔l
2! factor⇔l = factor⇔r
2! factor⇔r = factor⇔l
2! factorl⇔l = factorl⇔r
2! factorl⇔r = factorl⇔l
2! idl◎l = idl◎r
2! idl◎r = idl◎l
2! idr◎l = idr◎r
2! idr◎r = idr◎l
2! linv◎l = linv◎r
2! linv◎r = linv◎l
2! rinv◎l = rinv◎r
2! rinv◎r = rinv◎l
2! unite₊l⇔l = unite₊l⇔r
2! unite₊l⇔r = unite₊l⇔l
2! uniti₊l⇔l = uniti₊l⇔r
2! uniti₊l⇔r = uniti₊l⇔l
2! unite₊r⇔l = unite₊r⇔r
2! unite₊r⇔r = unite₊r⇔l
2! uniti₊r⇔l = uniti₊r⇔r
2! uniti₊r⇔r = uniti₊r⇔l
2! swapl₊⇔ = swapr₊⇔
2! swapr₊⇔ = swapl₊⇔
2! unitel⋆⇔l = uniter⋆⇔l
2! uniter⋆⇔l = unitel⋆⇔l
2! unitil⋆⇔l = unitir⋆⇔l
2! unitir⋆⇔l = unitil⋆⇔l
2! unitel⋆⇔r = uniter⋆⇔r
2! uniter⋆⇔r = unitel⋆⇔r
2! unitil⋆⇔r = unitir⋆⇔r
2! unitir⋆⇔r = unitil⋆⇔r
2! swapl⋆⇔ = swapr⋆⇔
2! swapr⋆⇔ = swapl⋆⇔
2! id⇔ = id⇔
2! (α ⊡ β) = (2! α) ⊡ (2! β)
2! (trans⇔ α β) = trans⇔ (2! β) (2! α)
2! (resp⊕⇔ α β) = resp⊕⇔ (2! α) (2! β)
2! (resp⊗⇔ α β) = resp⊗⇔ (2! α) (2! β)
2! id⟷⊕id⟷⇔ = split⊕-id⟷
2! split⊕-id⟷ = id⟷⊕id⟷⇔
2! hom⊕◎⇔ = hom◎⊕⇔
2! hom◎⊕⇔ = hom⊕◎⇔
2! id⟷⊗id⟷⇔ = split⊗-id⟷
2! split⊗-id⟷ = id⟷⊗id⟷⇔
2! hom⊗◎⇔ = hom◎⊗⇔
2! hom◎⊗⇔ = hom⊗◎⇔
2! triangle⊕l = triangle⊕r
2! triangle⊕r = triangle⊕l
2! triangle⊗l = triangle⊗r
2! triangle⊗r = triangle⊗l
2! pentagon⊕l = pentagon⊕r
2! pentagon⊕r = pentagon⊕l
2! pentagon⊗l = pentagon⊗r
2! pentagon⊗r = pentagon⊗l
2! unite₊l-coh-l = unite₊l-coh-r
2! unite₊l-coh-r = unite₊l-coh-l
2! unite⋆l-coh-l = unite⋆l-coh-r
2! unite⋆l-coh-r = unite⋆l-coh-l
2! hexagonr⊕l = hexagonr⊕r
2! hexagonr⊕r = hexagonr⊕l
2! hexagonl⊕l = hexagonl⊕r
2! hexagonl⊕r = hexagonl⊕l
2! hexagonr⊗l = hexagonr⊗r
2! hexagonr⊗r = hexagonr⊗l
2! hexagonl⊗l = hexagonl⊗r
2! hexagonl⊗r = hexagonl⊗l
2! absorbl⇔l = absorbl⇔r
2! absorbl⇔r = absorbl⇔l
2! absorbr⇔l = absorbr⇔r
2! absorbr⇔r = absorbr⇔l
2! factorzl⇔l = factorzl⇔r
2! factorzl⇔r = factorzl⇔l
2! factorzr⇔l = factorzr⇔r
2! factorzr⇔r = factorzr⇔l
2! swap₊distl⇔l = swap₊distl⇔r
2! swap₊distl⇔r = swap₊distl⇔l
2! dist-swap⋆⇔l = dist-swap⋆⇔r
2! dist-swap⋆⇔r = dist-swap⋆⇔l
2! assocl₊-dist-dist⇔l = assocl₊-dist-dist⇔r
2! assocl₊-dist-dist⇔r = assocl₊-dist-dist⇔l
2! assocl⋆-distl⇔l = assocl⋆-distl⇔r
2! assocl⋆-distl⇔r = assocl⋆-distl⇔l
2! absorbr0-absorbl0⇔ = absorbl0-absorbr0⇔
2! absorbl0-absorbr0⇔ = absorbr0-absorbl0⇔
2! absorbr⇔distl-absorb-unite = distl-absorb-unite⇔absorbr
2! distl-absorb-unite⇔absorbr = absorbr⇔distl-absorb-unite
2! unite⋆r0-absorbr1⇔ = absorbr1-unite⋆r-⇔
2! absorbr1-unite⋆r-⇔ = unite⋆r0-absorbr1⇔
2! absorbl≡swap⋆◎absorbr = swap⋆◎absorbr≡absorbl
2! swap⋆◎absorbr≡absorbl = absorbl≡swap⋆◎absorbr
2! absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr = 
    [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr
2!  [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr = 
    absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr
2! [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr =
    assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl
2! assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl =
    [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr
2! elim⊥-A[0⊕B]⇔l = elim⊥-A[0⊕B]⇔r
2! elim⊥-A[0⊕B]⇔r = elim⊥-A[0⊕B]⇔l
2! elim⊥-1[A⊕B]⇔l = elim⊥-1[A⊕B]⇔r
2! elim⊥-1[A⊕B]⇔r = elim⊥-1[A⊕B]⇔l
2! fully-distribute⇔l = fully-distribute⇔r
2! fully-distribute⇔r = fully-distribute⇔l

-- 0-dimensional evaluator

ap : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧
ap unite₊l (inj₁ ())
ap unite₊l (inj₂ v) = v
ap uniti₊l v = inj₂ v
ap unite₊r (inj₁ x) = x
ap unite₊r (inj₂ ())
ap uniti₊r v = inj₁ v
ap swap₊ (inj₁ v) = inj₂ v
ap swap₊ (inj₂ v) = inj₁ v
ap assocl₊ (inj₁ v) = inj₁ (inj₁ v)
ap assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
ap assocl₊ (inj₂ (inj₂ v)) = inj₂ v
ap assocr₊ (inj₁ (inj₁ v)) = inj₁ v
ap assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
ap assocr₊ (inj₂ v) = inj₂ (inj₂ v)
ap unite⋆l (tt , v) = v
ap uniti⋆l v = (tt , v)
ap unite⋆r (v , tt) = v
ap uniti⋆r v = v , tt
ap swap⋆ (v₁ , v₂) = (v₂ , v₁)
ap assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
ap assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
ap absorbr (x , _) = x
ap absorbl (_ , y) = y
ap factorzl ()
ap factorzr ()
ap dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
ap dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
ap factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
ap factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
ap distl (v , inj₁ x) = inj₁ (v , x)
ap distl (v , inj₂ y) = inj₂ (v , y)
ap factorl (inj₁ (x , y)) = x , inj₁ y
ap factorl (inj₂ (x , y)) = x , inj₂ y
ap id⟷ v = v
ap (c₁ ◎ c₂) v = ap c₂ (ap c₁ v)
ap (c₁ ⊕ c₂) (inj₁ v) = inj₁ (ap c₁ v)
ap (c₁ ⊕ c₂) (inj₂ v) = inj₂ (ap c₂ v)
ap (c₁ ⊗ c₂) (v₁ , v₂) = (ap c₁ v₁ , ap c₂ v₂)

-- useful to have the backwards ap too

ap! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₂ ⟧ → ⟦ t₁ ⟧
ap! unite₊l x = inj₂ x
ap! uniti₊l (inj₁ ())
ap! uniti₊l (inj₂ y) = y
ap! unite₊r v = inj₁ v
ap! uniti₊r (inj₁ x) = x
ap! uniti₊r (inj₂ ())
ap! swap₊ (inj₁ x) = inj₂ x
ap! swap₊ (inj₂ y) = inj₁ y
ap! assocl₊ (inj₁ (inj₁ x)) = inj₁ x
ap! assocl₊ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
ap! assocl₊ (inj₂ y) = inj₂ (inj₂ y)
ap! assocr₊ (inj₁ x) = inj₁ (inj₁ x)
ap! assocr₊ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
ap! assocr₊ (inj₂ (inj₂ y)) = inj₂ y
ap! unite⋆l x = tt , x
ap! uniti⋆l (tt , x) = x
ap! unite⋆r v = v , tt
ap! uniti⋆r (v , tt) = v
ap! swap⋆ (x , y) = y , x
ap! assocl⋆ ((x , y) , z) = x , y , z
ap! assocr⋆ (x , y , z) = (x , y) , z
ap! absorbr ()
ap! absorbl ()
ap! factorzr (_ , x) = x
ap! factorzl (x , _) = x
ap! dist (inj₁ (x , y)) = inj₁ x , y
ap! dist (inj₂ (x , y)) = inj₂ x , y
ap! factor (inj₁ x , z) = inj₁ (x , z)
ap! factor (inj₂ y , z) = inj₂ (y , z)
ap! distl (inj₁ (x , y)) = x , inj₁ y
ap! distl (inj₂ (x , y)) = x , inj₂ y
ap! factorl (v , inj₁ x) = inj₁ (v , x)
ap! factorl (v , inj₂ y) = inj₂ (v , y)
ap! id⟷ x = x
ap! (c₀ ◎ c₁) x = ap! c₀ (ap! c₁ x)
ap! (c₀ ⊕ c₁) (inj₁ x) = inj₁ (ap! c₀ x)
ap! (c₀ ⊕ c₁) (inj₂ y) = inj₂ (ap! c₁ y)
ap! (c₀ ⊗ c₁) (x , y) = ap! c₀ x , ap! c₁ y

postulate -- available in pi-dual; waiting for fork
  ap∼  : {τ : U} {v : ⟦ τ ⟧} {p₁ p₂ : τ ⟷ τ} → (p₁ ⇔ p₂) → ap p₁ v P.≡ ap p₂ v

-- Permutation to "poset-style" groupoid

compose : {τ : U} → (k : ℕ) → (p : τ ⟷ τ) → (τ ⟷ τ)
compose 0 p = id⟷
compose (suc k) p = p ◎ compose k p 

compose+ : {τ : U} {p : τ ⟷ τ} → (k₁ k₂ : ℕ) →
           (compose k₁ p ◎ compose k₂ p) ⇔ compose (k₁ + k₂) p
compose+ {p = p} 0 k₂ = idl◎l 
compose+ (suc k₁) k₂ = trans⇔ assoc◎r (id⇔ ⊡ (compose+ k₁ k₂))

compose≡ : {τ : U} {v₁ v₂ v₃ : ⟦ τ ⟧} {p : τ ⟷ τ} → (k₁ k₂ : ℕ)
  (a₁ : ap (compose k₁ p) v₁ P.≡ v₂) → 
  (a₂ : ap (compose k₂ p) v₂ P.≡ v₃) → 
  (ap (compose (k₁ + k₂) p) v₁ P.≡ v₃)
compose≡ {p = p} k₁ k₂ a₁ a₂ =
  (P.trans
    (ap∼ (2! (compose+ k₁ k₂)))
    (P.trans (P.cong (λ h → ap (compose k₂ p) h) a₁) a₂))

-- We are using the trivial relation on morphisms but we still take
-- the group structure of the permutation into account as we have that
-- for any p, there exist j and k such that pʲ ◎ !pᵏ is id
--
-- We could consider using pointed 1-combinators •[ τ₁ , v₁ ] ⟷ •[ τ₂
-- , v₂ ] and use a version of ⇔ to equate pointed 1-combinators.
-- This assumes that the level 2 combinators ⇔ are rich enough to
-- prove that for a permutation p of order k, we have compose k p ⇔ p

p⇒C : {τ : U} (p : τ ⟷ τ) → Category lzero lzero lzero
p⇒C {τ} p = record {
     Obj = ⟦ τ ⟧ 
   ; _⇒_ = λ v₁ v₂ → Σ[ k ∈ ℕ ] (ap (compose k p) v₁ P.≡ v₂)
   ; _≡_ = λ _ _ → ⊤
   ; id = (0 , P.refl)
   ; _∘_ = λ { {v₁} {v₂} {v₃} (k₂ , a₂) (k₁ , a₁) → (k₁ + k₂ , compose≡ k₁ k₂ a₁ a₂) }
   ; assoc = tt 
   ; identityˡ = tt 
   ; identityʳ = tt 
   ; equiv = record { refl = tt; sym = λ _ → tt; trans = λ _ _ → tt } 
   ; ∘-resp-≡ = λ _ _ → tt 
   }

p!p⇒C : {τ : U} (p : τ ⟷ τ) → Category lzero lzero lzero
p!p⇒C {τ} p = record {
     Obj = ⟦ τ ⟧ 
   ; _⇒_ = λ v₁ v₂ → (Σ[ j ∈ ℕ ] (ap (compose j p) v₁ P.≡ v₂)) ×
                     (Σ[ k ∈ ℕ ] (ap (compose k (! p)) v₁ P.≡ v₂))
   ; _≡_ = λ _ _ → ⊤
   ; id = ((0 , P.refl) , (0 , P.refl))
   ; _∘_ = λ { {v₁} {v₂} {v₃} ((j₂ , a₂₃) , (k₂ , b₂₃)) ((j₁ , a₁₂) , (k₁ , b₁₂)) →
             ((j₁ + j₂ , compose≡ j₁ j₂ a₁₂ a₂₃) , (k₁ + k₂ , compose≡ k₁ k₂ b₁₂ b₂₃)) }
   ; assoc = tt
   ; identityˡ = tt
   ; identityʳ = tt
   ; equiv = record { refl = tt; sym = λ _ → tt; trans = λ _ _ → tt } 
   ; ∘-resp-≡ = λ _ _ → tt 
   }

postulate -- available in pi-dual; waiting for fork
  ap!≡ : {τ : U} {v₁ v₂ : ⟦ τ ⟧} {p : τ ⟷ τ} → (ap p v₁ P.≡ v₂) → (ap (! p) v₂ P.≡ v₁)
  ap≡ : {τ : U} {v₁ v₂ : ⟦ τ ⟧} {p : τ ⟷ τ} → (ap (! p) v₁ P.≡ v₂) → (ap p v₂ P.≡ v₁)
  !!   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → ! (! c) P.≡ c

composeAssoc : {τ : U} {p : τ ⟷ τ} → (k : ℕ) →
               p ◎ compose k p ⇔ compose k p ◎ p
composeAssoc ℕ.zero = trans⇔ idr◎l idl◎r
composeAssoc (ℕ.suc k) = trans⇔ (id⇔ ⊡ (composeAssoc k)) assoc◎l                

reverse◎ : {τ : U} {p : τ ⟷ τ} → (k : ℕ) →
           ! (compose k p) ⇔ compose k (! p)
reverse◎ ℕ.zero = id⇔ 
reverse◎ {p = p} (ℕ.suc k) =
  trans⇔ (reverse◎ k ⊡ id⇔ ) (2! (composeAssoc {p = ! p} k))

reverse : {τ : U} {v₁ v₂ : ⟦ τ ⟧} {p : τ ⟷ τ} → (k : ℕ) →
          ap (compose k p) v₁ P.≡ v₂ →
          ap (compose k (! p)) v₂ P.≡ v₁
reverse {τ} {v₁} {v₂} {p} k pkv₁≡v₂ =
  P.trans (ap∼ (2! (reverse◎ k))) (ap!≡ {τ} {v₁} {v₂} {compose k p} pkv₁≡v₂) 

p⇒G : {τ : U} (p : τ ⟷ τ) → Groupoid (p!p⇒C p)
p⇒G {τ} p = record
  { _⁻¹ =
    λ { {v₁} {v₂} ((j , a) , (k , b)) →
      (( k , P.subst (λ h → ap (compose k h) v₂ P.≡ v₁) !! (reverse k b) ) ,
       (j , reverse j a)) } 
  ; iso = record {
    isoˡ = tt;
    isoʳ = tt
    }
  }
