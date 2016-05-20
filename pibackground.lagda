\DeclareUnicodeCharacter{738}{${}^S$}

\AgdaHide{
\begin{code}
module pibackground where

open import Data.Empty using (⊥) 
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true; _∧_; if_then_else_)
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Nat.LCM using (lcm)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Vec
  using (Vec; []; _∷_; _++_; concat; foldr)
  renaming (map to mapV)

open import Function using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_)

infix  30 _⟷_
infix  30 _⇔_
infixr 50 _◎_

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Background}
 
\amr{collect everything related to pi here and also talk about order
of permutations and introduce that here too}

%%%%%
\subsection{$\Pi$: Syntax and Operational Semantics} 

\begin{code} 
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

data _⟷_ : U → U → Set where
  unite₊l : {t : U} →
    PLUS ZERO t ⟷ t
  uniti₊l : {t : U} →
    t ⟷ PLUS ZERO t
  unite₊r : {t : U} →
    PLUS t ZERO ⟷ t
  uniti₊r : {t : U} →
    t ⟷ PLUS t ZERO
  swap₊   : {t₁ t₂ : U} →
    PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : U} →
    PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  assocr₊ : {t₁ t₂ t₃ : U} →
    PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆l  : {t : U} →
    TIMES ONE t ⟷ t
  uniti⋆l  : {t : U} →
    t ⟷ TIMES ONE t
  unite⋆r : {t : U} →
    TIMES t ONE ⟷ t
  uniti⋆r : {t : U} →
    t ⟷ TIMES t ONE
  swap⋆   : {t₁ t₂ : U} →
    TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : U} →
    TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  assocr⋆ : {t₁ t₂ t₃ : U} →
    TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  absorbr : {t : U} →
    TIMES ZERO t ⟷ ZERO
  absorbl : {t : U} →
    TIMES t ZERO ⟷ ZERO
  factorzr : {t : U} →
    ZERO ⟷ TIMES t ZERO
  factorzl : {t : U} →
    ZERO ⟷ TIMES ZERO t
  dist    : {t₁ t₂ t₃ : U} → 
    TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)
  factor  : {t₁ t₂ t₃ : U} → 
    PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  distl   : {t₁ t₂ t₃ : U } →
    TIMES t₁ (PLUS t₂ t₃) ⟷ PLUS (TIMES t₁ t₂) (TIMES t₁ t₃)
  factorl : {t₁ t₂ t₃ : U } →
    PLUS (TIMES t₁ t₂) (TIMES t₁ t₃) ⟷ TIMES t₁ (PLUS t₂ t₃)
  id⟷    : {t : U} →
    t ⟷ t
  _◎_     : {t₁ t₂ t₃ : U} →
    (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
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

\end{code}

%%%%%
\subsection{Level 2}

For $c_1, c_2 : \tau_1\leftrightarrow\tau_2$, we have level-2
combinators $\alpha : c_1 \Leftrightarrow c_2$ which are (quite messy)
equivalences of isomorphisms, and which happen to correspond to the
coherence conditions for rig groupoids.

Many of the level 2 combinators not used. These are the ones we need:

\begin{code}
data _⇔_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  assoc◎l : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
    (c₁ ◎ (c₂ ◎ c₃)) ⇔ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
    ((c₁ ◎ c₂) ◎ c₃) ⇔ (c₁ ◎ (c₂ ◎ c₃))
  idl◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} →
    (id⟷ ◎ c) ⇔ c
  idl◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} →
    c ⇔ id⟷ ◎ c
  idr◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} →
    (c ◎ id⟷) ⇔ c
  idr◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} →
    c ⇔ (c ◎ id⟷) 
  id⇔     : {t₁ t₂ : U} {c : t₁ ⟷ t₂} →
    c ⇔ c
  trans⇔  : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} → 
    (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊡_  : {t₁ t₂ t₃ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₁ ⟷ t₂} {c₄ : t₂ ⟷ t₃} →
    (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)

2! : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
2! assoc◎l = assoc◎r
2! assoc◎r = assoc◎l
2! idl◎l = idl◎r
2! idl◎r = idl◎l
2! idr◎l = idr◎r
2! idr◎r = idr◎l
2! id⇔ = id⇔
2! (α ⊡ β) = (2! α) ⊡ (2! β)
2! (trans⇔ α β) = trans⇔ (2! β) (2! α)
\end{code}

%%%%%
\subsection{Properties} 

\begin{code}

postulate 
  ap∼  : {τ : U} {v : ⟦ τ ⟧} {p₁ p₂ : τ ⟷ τ} → (p₁ ⇔ p₂) → ap p₁ v ≡ ap p₂ v
  ap!≡ : {τ : U} {v₁ v₂ : ⟦ τ ⟧} {p : τ ⟷ τ} → (ap p v₁ ≡ v₂) → (ap (! p) v₂ ≡ v₁)
  !!   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → ! (! c) ≡ c
  ⇔! : {τ₁ τ₂ : U} {p q : τ₁ ⟷ τ₂} → (α : p ⇔ q) → (! p ⇔ ! q)
  !!⇔ : {τ₁ τ₂ : U} {p : τ₁ ⟷ τ₂} → (! (! p) ⇔ p)
\end{code}


%%%%%
\subsection{Order} 

\begin{code}
data apⁿ {τ : U} (p : τ ⟷ τ) : ℕ → Set where
  ap¹ : apⁿ p 1
  apˢ : ∀ {n} → apⁿ p n → apⁿ p (suc n)

∣_∣ : U → ℕ
∣ ZERO ∣         = 0
∣ ONE ∣          = 1
∣ PLUS t₁ t₂ ∣   = ∣ t₁ ∣ + ∣ t₂ ∣
∣ TIMES t₁ t₂ ∣  = ∣ t₁ ∣ * ∣ t₂ ∣

elems : (τ : U) → Vec ⟦ τ ⟧ ∣ τ ∣ 
elems ZERO = []
elems ONE = tt ∷ []
elems (PLUS τ₁ τ₂) = mapV inj₁ (elems τ₁) ++ mapV inj₂ (elems τ₂)
elems (TIMES τ₁ τ₂) = concat (mapV (λ v₁ → mapV (λ v₂ → v₁ , v₂) (elems τ₂)) (elems τ₁))

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

postulate
  order-!≡ : {τ : U} {p : τ ⟷ τ} →  order τ p ≡ order τ (! p)

BOOL : U
BOOL = PLUS ONE ONE

THREEL : U
THREEL = PLUS BOOL ONE

p₁ p₂ p₃ p₄ p₅ p₆ : THREEL ⟷ THREEL
p₁ = id⟷                                -- (1 2 | 3) has order 1
p₂ = swap₊ ⊕ id⟷                        -- (2 1 | 3) has order 2
p₃ = assocr₊ ◎ (id⟷ ⊕ swap₊) ◎ assocl₊  -- (1 3 | 2) has order 2
p₄ = p₂ ◎ p₃                            -- (2 3 | 1) has order 3
p₅ = p₃ ◎ p₂                            -- (3 1 | 2) has order 3
p₆ = p₄ ◎ p₂                            -- (3 2 | 1) has order 2

\end{code}
