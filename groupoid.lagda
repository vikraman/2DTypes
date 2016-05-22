\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module groupoid where

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc)
open import Data.Integer
  using (ℤ; +_; -[1+_])
  renaming (-_ to ℤ-; suc to ℤsuc; _+_ to _ℤ+_)
open import Data.Product using (Σ; Σ-syntax; _,_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Universe using (Universe)

open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Monad using (Monad)
open import Comonad using (Comonad)

open import Categories.Product using (Product)

open import pibackground using (FT; UFT; 
  _⟷_; !; id⟷; _◎_;
  _⇔_; 2!; id⇔; trans⇔; assoc◎l; idr◎l; idl◎l; _⊡_)

infix 40 _^_ 

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Combinators as Groupoids}

Each combinator $p : \tau ⟷ \tau$ will give rise to two groupoids:
\begin{itemize}
\item one groupoid $\mathit{order}~p$ with objects $p^i$ and morphisms $⇔$, and 
\item another groupoid $\mathit{1/order}~p$ with one object and morphisms $p^i$ under $⇔$
\end{itemize}
There is also a third groupoid $\ag{\tau}{p}$ that is equivalent to
$\tau \boxtimes \mathit{1/order}~p$ and that is a conventional quotient type.

\begin{code}

-- First each p^i is an Agda type
-- Perm p i is the singleton type that only
--   contains p^i up to ⇔ 

_^_ : {τ : FT} → (p : τ ⟷ τ) → (k : ℤ) → (τ ⟷ τ)
p ^ (+ 0) = id⟷
p ^ (+ (suc k)) = p ◎ p ^ (+ k)
p ^ -[1+ 0 ] = ! p
p ^ (-[1+ (suc k) ]) = ! p ◎ p ^ -[1+ k ]

Perm : {τ : FT} → (p : τ ⟷ τ) (i : ℤ) → Set
Perm {τ} p i = Σ[ p' ∈ (τ ⟷ τ) ] (p' ^ i ⇔ p ^ i)

singleton : {τ : FT} → (p : τ ⟷ τ) → Perm p (+ 1)
singleton p = (p , id⇔)

-- orderC is the groupoid with objects p^i

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

-- p is a monad on (order p)

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

-- ! p is a comonad on (order p)

orderCom : {τ : FT} → (p : τ ⟷ τ) → Comonad (orderC p)
orderCom {τ} p = record {
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

-- the monad and comonad are inverses
-- idea regarding the significance of the
-- monad/comonad construction. Say we have
-- a combinator c : #p ⟷ #q that maps
-- p^i to q^j. Then we can use the q-monad
-- to write a combinator pc : #p ⟷ #q which
-- maps p^i to q^j using c and then to
-- q^(suc j) using the monad. We can use
-- the comonad to map p^i to p^(suc i) and
-- then to #q using c. So as an effect we can
-- constuct maps that move around #p and #q
-- using p and q.
--
-- A more general perspective: computations
-- happen in a context in the following sense:
-- say we have a collection of values v1, v2, ...
-- a computation takes vi to wi. In many cases,
-- the vi's form a structure of some kind and
-- so do the wi's. A monad focuses on the w's
-- structure and how to compose computations
-- on it. The comonad focuses on the v's structure
-- and how to compose computations on it. Some
-- people talk about monads expressing how to
-- affect the context and comonads expressing
-- what to expect from the context. 

-- moncom = ?

-- 1/orderC is the the groupoid with one object
--   and morphisms p^i

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

1/orderM : {τ : FT} (p : τ ⟷ τ) → Monad (1/orderC p)
1/orderM = {!!} 

1/orderCom : {τ : FT} (p : τ ⟷ τ) → Comonad (1/orderC p)
1/orderCom = {!!} 

-- τ // p

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

_//_ : (τ : FT) → (p : τ ⟷ τ) → Category _ _ _
τ // p = Product (discreteC (El τ)) (1/orderC p)
  where open Universe.Universe UFT

quotientG : (τ : FT) → (p : τ ⟷ τ) → Groupoid (τ // p)
quotientG = {!!} 

\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


