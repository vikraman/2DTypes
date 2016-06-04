\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module opsem where

open import Level using () renaming (zero to l0; suc to lsuc)
open import Universe using (Universe)
open import Data.Sum
open import Data.Product
open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc)
open import Data.Integer
  using (ℤ; +_; -[1+_])
  renaming (-_ to ℤ-; suc to ℤsuc; _+_ to _ℤ+_)
open import Rational+ renaming (_+_ to _ℚ+_; _*_ to _ℚ*_)
  hiding (_≤_; _≤?_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans)
open import Categories.Groupoid.Sum using () renaming (Sum to GSum)
open import Categories.Groupoid using () renaming (Product to GProduct)

infix 40 _^_ 

open import pibackground 

-- open import groupoid
data FT/ : Set where
  ⇑    : FT → FT/
  #    : {τ : FT} → (p : τ ⟷ τ) → FT/ 
  1/#  : {τ : FT} → (p : τ ⟷ τ) → FT/
  _⊞_  : FT/ → FT/ → FT/              
  _⊠_  : FT/ → FT/ → FT/
UG : Universe l0 (lsuc l0)
UG = record {
    U = FT/
 ;  El = λ T → Σ[ ℂ ∈ Category l0 l0 l0 ] (Groupoid ℂ)
 }
card : FT/ → ℚ
card (⇑ τ)      = mkRational ∣ τ ∣ 1 {tt}
card (# p)      = mkRational (order p) 1 {tt}
card (1/# p)    = mkRational 1 (order p) {order-nz}
card (T₁ ⊞ T₂)  = (card T₁) ℚ+ (card T₂)
card (T₁ ⊠ T₂)  = (card T₁) ℚ* (card T₂)
_^_ : {τ : FT} → (p : τ ⟷ τ) → (k : ℤ) → (τ ⟷ τ)
p ^ (+ 0) = id⟷
p ^ (+ (suc k)) = p ◎ p ^ (+ k)
p ^ -[1+ 0 ] = ! p
p ^ (-[1+ (suc k) ]) = ! p ◎ p ^ -[1+ k ]
Perm : {τ : FT} → (p : τ ⟷ τ) (i : ℤ) → Set
Perm {τ} p i = Σ[ p' ∈ (τ ⟷ τ) ] (p' ^ i ⇔ p ^ i)
singleton : {τ : FT} → (p : τ ⟷ τ) → Perm p (+ 1)
singleton p = (p , id⇔)
orderC : {τ : FT} → (p : τ ⟷ τ) → Category _ _ _
orderC {τ} p = record {
     Obj = Σ[ i ∈ ℤ ] (Perm p i)
   ; _⇒_ = λ { (m , (p , _)) (n , (q , _)) → p ^ m ⇔ q ^ n } 
   ; _≡_ = λ _ _ → ⊤ 
   ; id = id⇔ 
   ; _∘_ = λ α β → trans⇔ β α
   ; assoc = tt
   ; identityˡ = tt
   ; identityʳ = tt 
   ; equiv = record { refl = tt; sym = λ _ → tt; trans = λ _ _ → tt }
   ; ∘-resp-≡ = λ _ _ → tt  
   }
orderG : {τ : FT} → (p : τ ⟷ τ) → Groupoid (orderC p)
orderG {τ} p = record {
    _⁻¹ = 2!
  ; iso = record {
        isoˡ = tt
      ; isoʳ = tt
      }
  }
1/orderC : {τ : FT} (p : τ ⟷ τ) → Category _ _ _
1/orderC {τ} p = record {
     Obj = ⊤
    ; _⇒_ = λ _ _ → Σ[ i ∈ ℤ ] (Perm p i)
    ; _≡_ = λ { (m , (p , _)) (n , (q , _)) → p ^ m ⇔ q ^ n} 
    ; id = (+ 0 , singleton id⟷)
    ; _∘_ = λ { (m , (p , α)) (n , (q , β)) → (m ℤ+ n , (p ◎ q , {!!})) }
    ; assoc = {!!} -- assoc◎l 
    ; identityˡ = {!!} -- idr◎l 
    ; identityʳ = {!◎l !} -- idl◎l
    ; equiv = record { refl = id⇔; sym = 2!; trans = trans⇔ }
    ; ∘-resp-≡ = λ α β → {!!} -- β ⊡ α
    }
1/orderG : {τ : FT} (p : τ ⟷ τ) → Groupoid (1/orderC p)
1/orderG = {!!} 
discreteC : Set → Category _ _ _
discreteC S = record {
     Obj = S
    ; _⇒_ = λ s₁ s₂ → s₁ ≡ s₂
    ; _≡_ = λ _ _ → ⊤ 
    ; id = refl 
    ; _∘_ = λ { {A} {.A} {.A} refl refl → refl }
    ; assoc = tt 
    ; identityˡ = tt 
    ; identityʳ = tt 
    ; equiv = record { refl = tt; sym = λ _ → tt; trans = λ _ _ → tt }  
    ; ∘-resp-≡ = λ _ _ → tt 
    }
discreteG : (S : Set) → Groupoid (discreteC S)
discreteG S = record
  { _⁻¹ = λ { {A} {.A} refl → refl }
  ; iso = record { isoˡ = tt; isoʳ = tt }
  }
⟦_⟧/ : (T : FT/) → Universe.El UG T
⟦ ⇑ S ⟧/ = , discreteG (Universe.El UFT S)
⟦ # p ⟧/ = , orderG p
⟦ 1/# p ⟧/ = , 1/orderG p
⟦ T₁ ⊞ T₂ ⟧/ with ⟦ T₁ ⟧/ | ⟦ T₂ ⟧/
... | (_ , G₁) | (_ , G₂) = , GSum G₁ G₂
⟦ T₁ ⊠ T₂ ⟧/ with ⟦ T₁ ⟧/ | ⟦ T₂ ⟧/
... | (_ , G₁) | (_ , G₂) = , GProduct G₁ G₂
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Operational Semantics} 

%%%%%%%
\subsection{Combinators} 
  
Cardinality-preserving combinators: sound, not complete (see
limitations section), consistent.

\medskip

\begin{code}
-- do the trick of parametrizing the types so that we
-- don't have to repeat the constructors??

infix  30 _⇿_

data _⇿_ : FT/ → FT/ → Set where
  lift : {τ₁ τ₂ : FT} → (p : τ₁ ⟷ τ₂) → (⇑ τ₁ ⇿ ⇑ τ₂)
  η : {τ : FT} {p : τ ⟷ τ} → ⇑ ONE ⇿ (# p ⊠ 1/# p)
  ε : {τ : FT} {p : τ ⟷ τ} → (# p ⊠ 1/# p) ⇿ ⇑ ONE
  unite₊l/ : ∀ {T} → (⇑ ZERO ⊞ T) ⇿ T
  uniti₊l/ : ∀ {T} → T ⇿ (⇑ ZERO ⊞ T) 
  unite₊r/ : ∀ {T} → (T ⊞ ⇑ ZERO) ⇿ T
  uniti₊r/ : ∀ {T} → T ⇿ (T ⊞ ⇑ ZERO)
  swap₊/ : ∀ {T₁ T₂} → (T₁ ⊞ T₂) ⇿ (T₂ ⊞ T₁)
  assocl₊/ : ∀ {T₁ T₂ T₃} →
    (T₁ ⊞ (T₂ ⊞ T₃)) ⇿ ((T₁ ⊞ T₂) ⊞ T₃)
  assocr₊/ : ∀ {T₁ T₂ T₃} →
    ((T₁ ⊞ T₂) ⊞ T₃) ⇿ (T₁ ⊞ (T₂ ⊞ T₃))
  unite⋆l/  : ∀ {T} → (⇑ ONE ⊠ T) ⇿ T
  uniti⋆l/  : ∀ {T} → T ⇿ (⇑ ONE ⊠ T)
  unite⋆r/ : ∀ {T} → (T ⊠ ⇑ ONE) ⇿ T
  uniti⋆r/ : ∀ {T} → T ⇿ (T ⊠ ⇑ ONE)
  swap⋆/   : ∀ {T₁ T₂} → (T₁ ⊠ T₂) ⇿ (T₂ ⊠ T₁)
  assocl⋆/ : ∀ {T₁ T₂ T₃} →
    (T₁ ⊠ (T₂ ⊠ T₃)) ⇿ ((T₁ ⊠ T₂) ⊠ T₃)
  assocr⋆/ : ∀ {T₁ T₂ T₃} →
    ((T₁ ⊠ T₂) ⊠ T₃) ⇿ (T₁ ⊠ (T₂ ⊠ T₃))
  absorbr/ : ∀ {T} → (⇑ ZERO ⊠ T) ⇿ ⇑ ZERO
  absorbl/ : ∀ {T} → (T ⊠ ⇑ ZERO) ⇿ ⇑ ZERO
  factorzr/ : ∀ {T} → ⇑ ZERO ⇿ (T ⊠ ⇑ ZERO)
  factorzl/ : ∀ {T} → ⇑ ZERO ⇿ (⇑ ZERO ⊠ T)
  dist/    : ∀ {T₁ T₂ T₃} → 
    ((T₁ ⊞ T₂) ⊠ T₃) ⇿ ((T₁ ⊠ T₃) ⊞ (T₂ ⊠ T₃))
  factor/  : ∀ {T₁ T₂ T₃} → 
    ((T₁ ⊠ T₃) ⊞ (T₂ ⊠ T₃)) ⇿ ((T₁ ⊞ T₂) ⊠ T₃)
  distl/   : ∀ {T₁ T₂ T₃} →
    (T₁ ⊠ (T₂ ⊞ T₃)) ⇿ ((T₁ ⊠ T₂) ⊞ (T₁ ⊠ T₃))
  factorl/ : ∀ {T₁ T₂ T₃} →
    ((T₁ ⊠ T₂) ⊞ (T₁ ⊠ T₃)) ⇿ (T₁ ⊠ (T₂ ⊞ T₃))
  id⇿    : ∀ {T} → T ⇿ T
  _◎/_     : ∀ {T₁ T₂ T₃} → (T₁ ⇿ T₂) → (T₂ ⇿ T₃) → (T₁ ⇿ T₃)
  _⊕/_     : ∀ {T₁ T₂ T₃ T₄} → 
    (T₁ ⇿ T₃) → (T₂ ⇿ T₄) → ((T₁ ⊞ T₂) ⇿ (T₃ ⊞ T₄))
  _⊗/_     : ∀ {T₁ T₂ T₃ T₄} → 
    (T₁ ⇿ T₃) → (T₂ ⇿ T₄) → ((T₁ ⊠ T₂) ⇿ (T₃ ⊠ T₄))
\end{code}

\medskip

Consistency is defined in the following sense: If we allow arbitrary
functions then bad things happen as we can throw away the negative
information for example. In our reversible information-preserving
framework, the theory is consistent in the sense that not all types
are identified. This is easy to see as we only identify types that
have the same cardinality. This is evident for all the combinators
except for the new ones. For those new ones the only subtle situation
is with the empty type. Note however that there is no way to define
1/0 and no permutation has order 0. For 0 we have one permutation id
which has order 1. So if we try to use it, we will map 1 to 1 times
1/id which is fine. So if we always preserve types and trivially 1 and
0 have different cardinalities so there is no way to identify them and
we are consistent.

%%%%%%%
\subsection{Values}

Values of types FT/ are a pair of a point and automorphism on that
point. Note that the values of $\order{p}$ are things that represent
``apply this program $i$ times''

\medskip

\begin{code}
V : (T : FT/) → Set
V T = let ℂ , _ = ⟦ T ⟧/
          open Category ℂ
      in Σ[ v ∈ Obj ] (v ⇒ v)

-- Examples

v₁ : V (⇑ BOOL)
v₁ = (inj₁ tt , refl)

v₂ v₃ : V (# NOT)
v₂ = ((+ 0 , id⟷ , id⇔) , id⇔)
v₃ = ((+ 1 , NOT , id⇔) , id⇔)

v₄ v₅ : V (1/# NOT)
v₄ = (tt , (+ 1 , id⟷ , id⇔))
v₅ = (tt , (+ 1 , NOT , id⇔))

v₆ v₇ : V (# NOT ⊞ ⇑ BOOL)
v₆ = inj₁ (+ 0 , id⟷ , id⇔) , id⇔
v₇ = inj₂ (inj₁ tt) , refl

v₈ : V (# NOT ⊠ ⇑ BOOL)
v₈ = ((((+ 1 , NOT , id⇔) , (inj₁ tt))) , (id⇔ , refl))

v₉ : V (# NOT ⊠ 1/# NOT)
v₉ = ((((+ 1 , NOT , id⇔) , tt)) , (id⇔ , (+ 1 , id⟷ , id⇔)))
\end{code}

%%%%%%%
\subsection{Interpreter}

This is just a starting point. We cannot implement eta and epsilon
here. We have to define the inverse interpreter, contexts, and the
back-and-forth synchronization that eta and epsilon do together to
agree on the speculative choice.

\begin{code}
ap/ : {T₁ T₂ : FT/} → (T₁ ⇿ T₂) → V T₁ → V T₂
ap/ {⇑ τ₁} {⇑ τ₂} (lift c) (v , _) = let v' = ap c v in (v' , refl)
ap/ η (v , av) = {!!}
ap/ ε (v , av) = {!!}
ap/ unite₊l/ (inj₁ () , _)
ap/ unite₊l/ (inj₂ v , av) = (v , av)
ap/ uniti₊l/ (v , av) = (inj₂ v , av)
ap/ unite₊r/ (inj₁ v , av) = (v , av)
ap/ unite₊r/ (inj₂ () , _)
ap/ uniti₊r/ (v , av) = (inj₁ v , av)
ap/ swap₊/ (inj₁ v , av) = (inj₂ v , av)
ap/ swap₊/ (inj₂ v , av) = (inj₁ v , av)
ap/ assocl₊/ (v , av) = {!!}
ap/ assocr₊/ (v , av) = {!!}
ap/ unite⋆l/ (v , av) = {!!}
ap/ uniti⋆l/ (v , av) = {!!}
ap/ unite⋆r/ (v , av) = {!!}
ap/ uniti⋆r/ (v , av) = {!!}
ap/ swap⋆/ (v , av) = {!!}
ap/ assocl⋆/ (v , av) = {!!}
ap/ assocr⋆/ (v , av) = {!!}
ap/ absorbr/ (v , av) = {!!}
ap/ absorbl/ (v , av) = {!!}
ap/ factorzr/ (v , av) = {!!}
ap/ factorzl/ (v , av) = {!!}
ap/ dist/ (v , av) = {!!}
ap/ factor/ (v , av) = {!!}
ap/ distl/ (v , av) = {!!}
ap/ factorl/ (v , av) = {!!}
ap/ id⇿ (v , av) = (v , av)
ap/ (c₁ ◎/ c₂) (v , av) = {!!}
ap/ (c₁ ⊕/ c₂) (v , av) = {!!}
ap/ (c₁ ⊗/ c₂) (v , av) = {!!} 
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

