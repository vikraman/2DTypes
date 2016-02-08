module GroupAction where

open import Level renaming (zero to lzero; suc to lsuc)
open import Algebra
open import Algebra.Structures

open import Data.Unit
open import Data.Bool
open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (_+_)
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import Pi
open import Pi1

------------------------------------------------------------------------------
-- Define the unique group of 2 elements: the cyclic group ℤ₂

ℤ₂ : Group lzero lzero
ℤ₂ = record {
       Carrier = Bool
     ; _≈_ = _≡_
     ; _∙_  = _xor_
     ; ε = false
     ; _⁻¹ = id
     ; isGroup = record {
         isMonoid = record {
           isSemigroup = record {
             isEquivalence = isEquivalence
           ; assoc = λ { true true true → refl ;
                         true true false → refl ;
                         true false true → refl ;
                         true false false → refl ;
                         false true true → refl ;
                         false true false → refl ;
                         false false true → refl ;
                         false false false → refl
                       }
           ; ∙-cong = cong₂ _xor_
           }
         ; identity = ((λ a → refl) , (λ { true → refl ; false → refl }))
         }
       ; inverse = ((λ { true → refl ; false → refl }) ,
                    (λ { true → refl ; false → refl }))
       ; ⁻¹-cong = cong id
       }
     } 

-- For various sets S, let's define various possible group actions ρ :
-- ℤ₂ × S → S.  The resulting 'action groupoid' S //ρ ℤ₂ should always
-- have cardinality |S|/2 independently of ρ

record Action {c ℓ s} (G : Group c ℓ) (S : Set s) : Set (s ⊔ c) where
  open Group G
  field
    φ : Carrier × S → S 
    identityA : ∀ {x} → φ (ε , x) ≡ x
    compatibility : ∀ {g h x} → φ (g ∙ h , x) ≡ φ (g , φ (h , x))

0₁ : Fin 1
0₁ = zero

ρ-ℤ₂⊤ : Action ℤ₂ (Fin 1)
ρ-ℤ₂⊤ = record {
    φ = λ { (false , zero) → 0₁; 
            (true , zero) →  0₁;
            (_ , suc ())}
  ; identityA = λ { {suc ()}; {zero} → refl }
  ; compatibility = λ { {true} {true} {zero} → refl ;
                        {true} {false} {zero} → refl ;
                        {false} {true} {zero} → refl ;
                        {false} {false} {zero} → refl;
                        {_} {_} {suc ()}}
  }

0₂ 1₂ : Fin 2
0₂ = zero
1₂ = suc zero

ρ-ℤ₂Fin2-Id ρ-ℤ₂Fin2-Not : Action ℤ₂ (Fin 2)

ρ-ℤ₂Fin2-Id = record {
    φ = λ { (_ , n) → n }
  ; identityA = λ { {suc (suc ())};  {suc zero} → refl ; {zero} → refl }
  ; compatibility = λ { {true} {true} {suc zero} → refl ;
                        {true} {true} {zero} → refl ;
                        {true} {false} {suc zero} → refl ;
                        {true} {false} {zero} → refl ;
                        {false} {true} {suc zero} → refl ;
                        {false} {true} {zero} → refl ;
                        {false} {false} {suc zero} → refl ;
                        {false} {false} {zero} → refl;
                        {_} {_} {suc (suc ())}}
  }

-- Picture of the groupoid (Fin 2) //ρ-ℤ₂Fin2-Id ℤ₂
--
--       false,true          false,true
--          ----                ----
--          \  /                \  /
--           0₂                  1₂
--
-- So it has cardinarlity 2 * 1/2 = 1

not₂ : Fin 2 → Fin 2
not₂ zero = 1₂
not₂ (suc zero) = 0₂
not₂ (suc (suc ()))

ρ-ℤ₂Fin2-Not = record {
    φ = λ { (false , n) → n; (true , n) → not₂ n }
  ; identityA = λ { {suc (suc ())}; {suc zero} → refl ; {zero} → refl }
  ; compatibility = λ { {true} {true} {suc zero} → refl ;
                        {true} {true} {zero} → refl ;
                        {true} {false} {suc zero} → refl ;
                        {true} {false} {zero} → refl ;
                        {false} {true} {suc zero} → refl ;
                        {false} {true} {zero} → refl ;
                        {false} {false} {suc zero} → refl ;
                        {false} {false} {zero} → refl;
                        {_} {_} {suc (suc ())}}
  }

-- Picture of the groupoid (Fin 2) //ρ-ℤ₂Fin2-Not ℤ₂
--
--          false               false
--          ----                ----
--          \  /    true        \  /
--           0₂ ---------------> 1₂
--              <---------------
--                  true
--
-- This also has cardinarlity 1

------------------------------------------------------------------------------
-- Now repeat with our universe of types

BOOL : U
BOOL = PLUS ONE ONE

-- cyclic group of BOOL

-- prove the following in Pi1
postulate
  xxx : {a b : BOOL ⟷ BOOL} → (a ⇔ b) → (! a ⇔ ! b)

ℤ₁₊₁ : Group lzero lzero
ℤ₁₊₁ = record {
       Carrier = BOOL ⟷ BOOL
     ; _≈_ = _⇔_ 
     ; _∙_  = _◎_
     ; ε = id⟷
     ; _⁻¹ = ! 
     ; isGroup = record {
         isMonoid = record {
           isSemigroup = record {
             isEquivalence = ⇔Equiv 
           ; assoc = λ c₁ c₂ c₃ → assoc◎r  
           ; ∙-cong = _⊡_ 
           }
         ; identity = ((λ c → idl◎l) , (λ c → idr◎l))  
         }
       ; inverse = ((λ c → rinv◎l) , (λ c → linv◎l)) 
       ; ⁻¹-cong = λ {a} {b} c → xxx c 
       }
     } 


