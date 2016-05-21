\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module groupoid where

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc)
open import Data.Integer
  using (ℤ; +_; -[1+_])
  renaming (-_ to ℤ-; suc to ℤsuc)
open import Data.Product using (Σ; Σ-syntax; _,_)

open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Monad using (Monad)
open import Comonad using (Comonad)

open import pibackground using (FT;
  _⟷_; !; id⟷; _◎_;
  _⇔_; 2!; id⇔; trans⇔; _⊡_)

infix 40 _^_ 

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Combinators as Groupoids}

\begin{code}

-- Perm p i is the singleton type that only contains p^i up to ⇔ 

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

^suc : {τ : FT} {p : τ ⟷ τ} {i : ℤ} → p ^ ℤsuc i ⇔ p ◎ p ^ i
^suc = {!!}

^resp : {τ : FT} {p q : τ ⟷ τ} {i : ℤ} → (q ^ i ⇔ p ^ i) → (q ◎ q ^ i ⇔ p ◎ p ^ i)
^resp = {!!} 

orderM : {τ : FT} → (p : τ ⟷ τ) → Monad (orderC p)
orderM {τ} p = record {
    F = record {
          F₀ = λ { (i , (q , α)) →
                 (ℤsuc i , (q , trans⇔ (^suc {p = q} {i = i})
                                (trans⇔ (^resp {p = p} {q = q} {i = i} α)
                                (2! (^suc {p = p} {i = i})))))}
        ; F₁ = {!!}
        }
  ; η = record {
          η = {!!}
        ; commute = λ _ → tt
        }
  ; μ = record {
          η = {!!}
        ; commute = λ _ → tt
        }
  ; assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  }

orderCoM : {τ : FT} → (p : τ ⟷ τ) → Comonad (orderC p)
orderCoM {τ} p = record {
    F = record {
          F₀ = {!!} 
        ; F₁ = {!!}
        }
  ; η = record {
          η = {!!}
        ; commute = λ _ → tt
        }
  ; μ = record {
          η = {!!}
        ; commute = λ _ → tt
        }
  ; assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  }


\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


