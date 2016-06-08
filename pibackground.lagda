\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module pibackground where

open import Data.Empty using (⊥) 
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true; _∧_; if_then_else_)
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Nat.LCM using (lcm)
open import Rational+ using (NonZero)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Vec
  using (Vec; []; _∷_; _++_; concat; foldr)
  renaming (map to mapV)

open import Function using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Universe using (Universe)

infix  30 _⟷_
infix  30 _⇔_
infixr 50 _◎_

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Background}
 
\amr{Given that everything is mutually recursive, I suggest this
section to be presented in the mathematical metlanguage, not in
Agda. So let's remove all Agda code and explain the ideas.}

%%%%%
\subsection{$\Pi$ Syntax} 

Types FT, programs $⟷$, and equivalences $⇔$.

\begin{code} 

data FT : Set where
  ZERO   : FT
  ONE    : FT
  PLUS   : FT → FT → FT
  TIMES  : FT → FT → FT

data _⟷_ : FT → FT → Set where
  unite₊l : ∀ {t} → PLUS ZERO t ⟷ t
  uniti₊l : ∀ {t} → t ⟷ PLUS ZERO t
  unite₊r : ∀ {t} → PLUS t ZERO ⟷ t
  uniti₊r : ∀ {t} → t ⟷ PLUS t ZERO
  swap₊   : ∀ {t₁ t₂} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : ∀ {t₁ t₂ t₃} →
    PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  assocr₊ : ∀ {t₁ t₂ t₃} →
    PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆l  : ∀ {t} → TIMES ONE t ⟷ t
  uniti⋆l  : ∀ {t} → t ⟷ TIMES ONE t
  unite⋆r : ∀ {t} → TIMES t ONE ⟷ t
  uniti⋆r : ∀ {t} → t ⟷ TIMES t ONE
  swap⋆   : ∀ {t₁ t₂} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : ∀ {t₁ t₂ t₃} →
    TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  assocr⋆ : ∀ {t₁ t₂ t₃} →
    TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  absorbr : ∀ {t} → TIMES ZERO t ⟷ ZERO
  absorbl : ∀ {t} → TIMES t ZERO ⟷ ZERO
  factorzr : ∀ {t} → ZERO ⟷ TIMES t ZERO
  factorzl : ∀ {t} → ZERO ⟷ TIMES ZERO t
  dist    : ∀ {t₁ t₂ t₃} → 
    TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)
  factor  : ∀ {t₁ t₂ t₃} → 
    PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  distl   : ∀ {t₁ t₂ t₃} →
    TIMES t₁ (PLUS t₂ t₃) ⟷ PLUS (TIMES t₁ t₂) (TIMES t₁ t₃)
  factorl : ∀ {t₁ t₂ t₃} →
    PLUS (TIMES t₁ t₂) (TIMES t₁ t₃) ⟷ TIMES t₁ (PLUS t₂ t₃)
  id⟷    : ∀ {t} → t ⟷ t
  _◎_     : ∀ {t₁ t₂ t₃} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : ∀ {t₁ t₂ t₃ t₄} → 
    (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : ∀ {t₁ t₂ t₃ t₄} → 
    (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)

! : {t₁ t₂ : FT} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
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
\end{code}

For $c_1, c_2 : \tau_1\leftrightarrow\tau_2$, we have level-2
combinators $\alpha : c_1 \Leftrightarrow c_2$ which are equivalences
of isomorphisms, and which happen to correspond to the coherence
conditions for rig groupoids. Many of the level 2 combinators not
used. We only present the ones we use in this paper:

\begin{code}
data _⇔_ : {t₁ t₂ : FT} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  assoc◎l : ∀ {t₁ t₂ t₃ t₄} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
    (c₁ ◎ (c₂ ◎ c₃)) ⇔ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : ∀ {t₁ t₂ t₃ t₄} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
    ((c₁ ◎ c₂) ◎ c₃) ⇔ (c₁ ◎ (c₂ ◎ c₃))
  idl◎l   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    (id⟷ ◎ c) ⇔ c
  idl◎r   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    c ⇔ id⟷ ◎ c
  idr◎l   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    (c ◎ id⟷) ⇔ c
  idr◎r   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    c ⇔ (c ◎ id⟷) 
  id⇔     : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    c ⇔ c
  rinv◎l  : {t₁ t₂ : FT} {c : t₁ ⟷ t₂} → (! c ◎ c) ⇔ id⟷
  rinv◎r  : {t₁ t₂ : FT} {c : t₁ ⟷ t₂} → id⟷ ⇔ (! c ◎ c) 
  linv◎l  : {t₁ t₂ : FT} {c : t₁ ⟷ t₂} → (c ◎ ! c) ⇔ id⟷
  linv◎r  : {t₁ t₂ : FT} {c : t₁ ⟷ t₂} → id⟷ ⇔ (c ◎ ! c) 
  trans⇔  : ∀ {t₁ t₂} {c₁ c₂ c₃ : t₁ ⟷ t₂} → 
    (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊡_  : ∀ {t₁ t₂ t₃} {c₁ c₃ : t₁ ⟷ t₂} {c₂ c₄ : t₂ ⟷ t₃} → 
    (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {t₁ t₂ t₃ t₄ : FT} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  resp⊗⇔  : {t₁ t₂ t₃ t₄ : FT} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊗ c₂) ⇔ (c₃ ⊗ c₄)

2! : {t₁ t₂ : FT} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
2! assoc◎l = assoc◎r
2! assoc◎r = assoc◎l
2! idl◎l = idl◎r
2! idl◎r = idl◎l
2! idr◎l = idr◎r
2! idr◎r = idr◎l
2! rinv◎l = rinv◎r
2! rinv◎r = rinv◎l
2! linv◎l = linv◎r
2! linv◎r = linv◎l
2! id⇔ = id⇔
2! (α ⊡ β) = (2! α) ⊡ (2! β)
2! (trans⇔ α β) = trans⇔ (2! β) (2! α)
2! (resp⊕⇔ α β) = resp⊕⇔ (2! α) (2! β)
2! (resp⊗⇔ α β) = resp⊗⇔ (2! α) (2! β)

\end{code}

%%%%%
\subsection{Semantics}

\begin{code}

-- Denotation as finite sets

UFT : Universe _ _
UFT = record { U = FT; El = ⟦_⟧ }
  where
    ⟦_⟧ : FT → Set
    ⟦ ZERO ⟧         = ⊥ 
    ⟦ ONE ⟧          = ⊤
    ⟦ PLUS t₁ t₂ ⟧   = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
    ⟦ TIMES t₁ t₂ ⟧  = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

open Universe.Universe UFT

-- Operational semantics

postulate
  ap⁻¹ : {t₁ t₂ : FT} → (t₁ ⟷ t₂) → El t₂ → El t₁

ap : {t₁ t₂ : FT} → (t₁ ⟷ t₂) → El t₁ → El t₂
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
\subsection{Properties} 

\begin{code}

postulate 
  ap∼  : {τ : U} {v : El τ} {p₁ p₂ : τ ⟷ τ} →
    (p₁ ⇔ p₂) → ap p₁ v ≡ ap p₂ v
  ap!≡ : {τ : U} {v₁ v₂ : El τ} {p : τ ⟷ τ} →
    (ap p v₁ ≡ v₂) → (ap (! p) v₂ ≡ v₁)
  !!   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → ! (! c) ≡ c
  ⇔! : {τ₁ τ₂ : U} {p q : τ₁ ⟷ τ₂} → (α : p ⇔ q) → (! p ⇔ ! q)
  !!⇔ : {τ₁ τ₂ : U} {p : τ₁ ⟷ τ₂} → (! (! p) ⇔ p)
\end{code}


%%%%%
\subsection{Order of a Combinator} 

\begin{code}
∣_∣ : U → ℕ
∣ ZERO ∣         = 0
∣ ONE ∣          = 1
∣ PLUS t₁ t₂ ∣   = ∣ t₁ ∣ + ∣ t₂ ∣
∣ TIMES t₁ t₂ ∣  = ∣ t₁ ∣ * ∣ t₂ ∣

elems : (τ : U) → Vec (El τ) ∣ τ ∣ 
elems ZERO = []
elems ONE = tt ∷ []
elems (PLUS τ₁ τ₂) =
  mapV inj₁ (elems τ₁) ++ mapV inj₂ (elems τ₂)
elems (TIMES τ₁ τ₂) =
  concat
    (mapV
      (λ v₁ → mapV (λ v₂ → v₁ , v₂) (elems τ₂))
      (elems τ₁))

lcm' : ℕ → ℕ → ℕ
lcm' i j with lcm i j
... | k , _ = k

_==_ : {τ : U} → El τ → El τ → Bool
_==_ {ZERO} () ()
_==_ {ONE} tt tt = true
_==_ {PLUS τ τ'} (inj₁ x) (inj₁ y) = x == y
_==_ {PLUS τ τ'} (inj₁ x) (inj₂ y) = false
_==_ {PLUS τ τ'} (inj₂ x) (inj₁ y) = false
_==_ {PLUS τ τ'} (inj₂ x) (inj₂ y) = x == y
_==_ {TIMES τ τ'} (x , x') (y , y') = x == y ∧ x' == y'

{-# NON_TERMINATING #-}
order : {τ : U} (p : τ ⟷ τ) → ℕ
order {τ} p = foldr (λ _ → ℕ)
                (λ v o → lcm' o (go τ p v v 1)) 1 (elems τ)
  where go : (τ : U) (p : τ ⟷ τ) → El τ → El τ → ℕ → ℕ
        go τ p v v' n with ap p v'
        ... | v'' = if v == v'' then n else go τ p v v'' (suc n)

postulate
  order-nz : {τ : U} {p : τ ⟷ τ} → NonZero (order p)
  order-!≡ : {τ : U} {p : τ ⟷ τ} →  order p ≡ order (! p)

-- Conjecture:  p ⇔ q   implies  order p = order q
-- Corollary:   p ⇔ !q  implies  order p = order (! q)

-- The opposite is not true.

-- Example
-- p = (1 2 3 4)

-- compose p 0 = compose !p 0 = compose p 4 = compose !p 4
-- 1 -> 1
-- 2 -> 2
-- 3 -> 3
-- 4 -> 4

-- compose p 1  ***     compose !p 1
-- 1 -> 2       ***     1 -> 4
-- 2 -> 3       ***     2 -> 1
-- 3 -> 4       ***     3 -> 2
-- 4 -> 1       ***     4 -> 3

-- compose p 2  ***     compose !p 2
-- 1 -> 3       ***     1 -> 3
-- 2 -> 4       ***     2 -> 4
-- 3 -> 1       ***     3 -> 1
-- 4 -> 2       ***     4 -> 2

-- compose p 3  ***     compose !p 3
-- 1 -> 4       ***     1 -> 2
-- 2 -> 1       ***     2 -> 3
-- 3 -> 2       ***     3 -> 4
-- 4 -> 3       ***     4 -> 1

-- there is a morphism 1 -> 2 using
-- (compose p 1) and (compose !p 3)
-- p¹ is the same as !p³
-- p² is the same as !p²
-- p³ is the same as !p¹

\end{code}

%%%%%
\subsection{Examples}

\begin{code}

BOOL : U
BOOL = PLUS ONE ONE

THREEL : U
THREEL = PLUS BOOL ONE

BOOL² : U
BOOL² = TIMES BOOL BOOL

p₁ p₂ p₃ p₄ p₅ p₆ : THREEL ⟷ THREEL
p₁ = id⟷                                -- (1 2 | 3) has order 1
p₂ = swap₊ ⊕ id⟷                        -- (2 1 | 3) has order 2
p₃ = assocr₊ ◎ (id⟷ ⊕ swap₊) ◎ assocl₊  -- (1 3 | 2) has order 2
p₄ = p₂ ◎ p₃                            -- (2 3 | 1) has order 3
p₅ = p₃ ◎ p₂                            -- (3 1 | 2) has order 3
p₆ = p₄ ◎ p₂                            -- (3 2 | 1) has order 2

NOT : BOOL ⟷ BOOL -- has order 2
NOT = swap₊ 

CNOT : BOOL² ⟷ BOOL² -- has order 2
CNOT = dist ◎ (id⟷ ⊕ (id⟷ ⊗ NOT)) ◎ factor 

TOFFOLI : TIMES BOOL BOOL² ⟷ TIMES BOOL BOOL² -- has order 2
TOFFOLI = dist ◎ (id⟷ ⊕ (id⟷ ⊗ CNOT)) ◎ factor

\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
