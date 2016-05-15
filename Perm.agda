module Perm where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Relation.Binary
open import Data.Bool

data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

toℕ : U → ℕ
toℕ ZERO = 0
toℕ ONE = 1
toℕ (PLUS t₁ t₂) = toℕ t₁ + toℕ t₂
toℕ (TIMES t₁ t₂) = toℕ t₁ * toℕ t₂

⟦_⟧ : U → Set
⟦ ZERO ⟧         = ⊥
⟦ ONE ⟧          = ⊤
⟦ PLUS t₁ t₂ ⟧   = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧  = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

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

data apⁿ {τ : U} (p : τ ⟷ τ) : ℕ → Set where
  ap¹ : apⁿ p 1
  apˢ : ∀ {n} → apⁿ p n → apⁿ p (suc n)

module _ {τ : U} {p : τ ⟷ τ} where
  ⟦_⟧apⁿ : {n : ℕ} → apⁿ p n → ⟦ τ ⟧ → ⟦ τ ⟧
  ⟦ ap¹ ⟧apⁿ v = ap p v
  ⟦ apˢ a ⟧apⁿ v = ap p (⟦ a ⟧apⁿ v)

-- open import Relation.Binary.PropositionalEquality

-- order : (τ : U) (p : τ ⟷ τ) → (v : ⟦ τ ⟧) → Σ[ n ∈ ℕ ] Σ[ a ∈ apⁿ p n ] ⟦ a ⟧apⁿ v ≡ v
-- order ZERO id⟷ ()
-- order ZERO (p₁ ◎ p₂) ()
-- order ONE id⟷ tt = 1 , ap¹ , refl
-- order ONE (p₁ ◎ p₂) tt = 1 , ap¹ , refl
-- order (PLUS τ .τ) swap₊ (inj₁ x) = 2 , apˢ ap¹ , refl
-- order (PLUS τ .τ) swap₊ (inj₂ y) = 2 , apˢ ap¹ , refl
-- order (PLUS τ₁ τ₂) id⟷ (inj₁ x) = 1 , ap¹ , refl
-- order (PLUS τ₁ τ₂) id⟷ (inj₂ y) = 1 , ap¹ , refl
-- order (PLUS τ₁ τ₂) (p₁ ◎ p₂) (inj₁ x) = let (n₁ , a₁ , pf₁) = order τ₁ {!!} x
--                                         in {!!} , {!!} , {!!}
-- order (PLUS τ₁ τ₂) (p₁ ◎ p₂) (inj₂ y) = {!!}
-- order (PLUS τ₁ τ₂) (p₁ ⊕ p₂) (inj₁ x) = {!!}
-- order (PLUS τ₁ τ₂) (p₁ ⊕ p₂) (inj₂ y) = {!!}
-- order (TIMES τ .τ) swap⋆ (proj₁ , proj₂) = 2 , apˢ ap¹ , refl
-- order (TIMES τ₁ τ₂) id⟷ (proj₁ , proj₂) = 1 , ap¹ , refl
-- order (TIMES τ₁ τ₂) (p₁ ◎ p₂) (proj₁ , proj₂) = {!!}
-- order (TIMES τ₁ τ₂) (p₁ ⊗ p₂) (proj₁ , proj₂) = {!!}

open import Data.Vec renaming (map to mapV)

elems : (τ : U) → Vec ⟦ τ ⟧ (toℕ τ)
elems ZERO = []
elems ONE = tt ∷ []
elems (PLUS τ₁ τ₂) = mapV inj₁ (elems τ₁) ++ mapV inj₂ (elems τ₂)
elems (TIMES τ₁ τ₂) = concat (mapV (λ v₁ → mapV (λ v₂ → v₁ , v₂) (elems τ₂)) (elems τ₁))

open import Data.Nat.LCM

lcm' : ℕ → ℕ → ℕ
lcm' i j with lcm i j
... | k , _ = k

_==_ : {τ : U} → ⟦ τ ⟧ → ⟦ τ ⟧ → Bool
_==_ {ZERO} () ()
_==_ {ONE} tt tt = true
_==_ {PLUS τ τ'} (inj₁ x) (inj₁ y) = x == y
_==_ {PLUS τ τ'} (inj₁ x) (inj₂ y) = false
_==_ {PLUS τ τ'} (inj₂ x) (inj₁ y) = false
_==_ {PLUS τ τ'} (inj₂ x) (inj₂ y) = x == y
_==_ {TIMES τ τ'} (x , x') (y , y') = x == y ∧ x' == y'

{-# NON_TERMINATING #-}
order : (τ : U) (p : τ ⟷ τ) → ℕ
order τ p = foldr (λ _ → ℕ) (λ v o → lcm' o (go τ p v v 1)) 1 (elems τ)
  where go : (τ : U) (p : τ ⟷ τ) → ⟦ τ ⟧ → ⟦ τ ⟧ → ℕ → ℕ
        go τ p v v' n with ap p v'
        ... | v'' = if v == v'' then n else go τ p v v'' (suc n)

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Data.String
open import Data.Nat.Show renaming (show to showℕ)
open import Function

postulate
  putStrLn : String -> IO ⊤
{-# IMPORT Data.Text.IO #-}
{-# COMPILED putStrLn Data.Text.IO.putStrLn #-}

print : ℕ → IO ⊤
print = putStrLn ∘ showℕ

BOOL : U
BOOL = PLUS ONE ONE

THREEL : U
THREEL = PLUS BOOL ONE

p₁ p₂ p₃ p₄ p₅ p₆ : THREEL ⟷ THREEL
p₁ = id⟷ -- (1 2 | 3)
p₂ = swap₊ ⊕ id⟷ -- (2 1 | 3)
p₃ = assocr₊ ◎ (id⟷ ⊕ swap₊) ◎ assocl₊ -- (1 3 | 2)
p₄ = p₂ ◎ p₃ -- (2 3 | 1)
p₅ = p₃ ◎ p₂ -- (3 1 | 2)
p₆ = p₄ ◎ p₂ -- (3 2 | 1)

main : IO ⊤
main = print $ order THREEL p₄
