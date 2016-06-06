\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module opsem where

open import Level using () renaming (zero to l0; suc to lsuc)
open import Universe using (Universe)
open import Data.Bool
open import Data.Sum hiding ([_,_])
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
  using (_≡_; refl; trans; subst)
open import Categories.Groupoid.Sum using () renaming (Sum to GSum)
open import Categories.Groupoid using () renaming (Product to GProduct)

open import pibackground 
open import groupoid
open import pifrac

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Operational Semantics} 

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

-- Examples:

-- When we have a discrete category, the objects are values and we
-- want a morphism from every value to itself so the morphisms are
-- propositional equalities; when we have the category 1/# p, there is
-- only a trivial object and the morphisms are combinators; when we
-- have the category #p, the objects are combinators and the morphisms
-- are 2-combinators. So we have a progression of objects: values, tt,
-- combinators and a corresponding progression of morphisms: refl,
-- combinators, and 2-combinators. And then we have sums and products
-- of these things.

-- Abbreviations: 

-- discrete values

dv : {τ : FT} → Universe.El UFT τ → V (⇑ τ)
dv v = (v , refl)

-- fractional values

fv : {τ : FT} → (p : τ ⟷ τ) (i : ℤ) → V (1/# p)
fv p i = (tt , perm i (p ^ i) id⇔)

-- combinator values

cv : {τ : FT} → (p : τ ⟷ τ) (i : ℤ) → V (# p)
cv p i = (perm i (p ^ i) id⇔ , id⇔)

-- left and right injections

inj₁/ : {T₁ T₂ : FT/} → V T₁ → V (T₁ ⊞ T₂)
inj₁/ (v , av) = (inj₁ v , av)

inj₂/ : {T₁ T₂ : FT/} → V T₂ → V (T₁ ⊞ T₂)
inj₂/ (v , av) = (inj₂ v , av)

-- pairing

[_,_] : {T₁ T₂ : FT/} → V T₁ → V T₂ → V (T₁ ⊠ T₂)
[ (v₁ , av₁) , (v₂ , av₂) ] = ((v₁ , v₂) , (av₁ , av₂))

--

v₁ : V (⇑ BOOL)
v₁ = dv (inj₁ tt)

v₂ v₃ : V (# NOT)
v₂ = cv NOT (+ 0)
v₃ = cv NOT (+ 1)

v₄ v₅ : V (1/# NOT)
v₄ = fv NOT (+ 0)
v₅ = fv NOT (+ 1)

v₆ v₇ : V (# NOT ⊞ ⇑ BOOL)
v₆ = inj₁/ {T₁ = # NOT} {T₂ = ⇑ BOOL} v₂
v₇ = inj₂/ {T₁ = # NOT} {T₂ = ⇑ BOOL} v₁

v₈ : V (# NOT ⊠ ⇑ BOOL)
v₈ = [_,_] {T₁ = # NOT} {T₂ = ⇑ BOOL} v₂ v₁

v₉ : V (# NOT ⊠ 1/# NOT)
v₉ = [_,_] {T₁ = # NOT} {T₂ = 1/# NOT} v₂ v₅ -- mismatched pair

\end{code}

%%%%%%%
\subsection{Interpreter}

\begin{code}
-- Context T1 T2 T3 : missing T1 ⇿ T2 combinator;
-- returns T3 as final answer

data Context : FT/ → FT/ → FT/ → Set where
  Empty : {T : FT/} → Context T T T
  Fst : {T₁ T₂ T₃ T : FT/} →
    (C : Context T₁ T₃ T) → (P₂ : T₂ ⇿ T₃) → Context T₁ T₂ T
  Snd : {T₁ T₂ T₃ T : FT/} →
    (P₁ : T₁ ⇿ T₂) → (C : Context T₁ T₃ T) → Context T₂ T₃ T
  L× : {T₁ T₂ T₃ T₄ T : FT/} →
    (C : Context (T₁ ⊠ T₂) (T₃ ⊠ T₄) T) →
    (P₂ : T₂ ⇿ T₄) → V T₂ → Context T₁ T₃ T
  R× : {T₁ T₂ T₃ T₄ T : FT/} →
    (P₁ : T₁ ⇿ T₃) → V T₃ →
    (C : Context (T₁ ⊠ T₂) (T₃ ⊠ T₄) T) → Context T₂ T₄ T
  L+ : {T₁ T₂ T₃ T₄ T : FT/} →
    (C : Context (T₁ ⊞ T₂) (T₃ ⊞ T₄) T) → (P₂ : T₂ ⇿ T₄) → 
    Context T₁ T₃ T
  R+ : {T₁ T₂ T₃ T₄ T : FT/} →
    (P₁ : T₁ ⇿ T₃) → (C : Context (T₁ ⊞ T₂) (T₃ ⊞ T₄) T) → 
    Context T₂ T₄ T

data State : FT/ → Set where
  Enter : {T₁ T₂ T : FT/} →
    (P : T₁ ⇿ T₂) → V T₁ → Context T₁ T₂ T → State T
  Exit : {T₁ T₂ T : FT/} →
    (P : T₁ ⇿ T₂) → V T₂ → Context T₁ T₂ T → State T

data Dir : Set where
  Fwd : Dir
  Bck : Dir
  Done : Dir

-- stepForward 

-- Trivial implementation of eta/epsilon that does
-- type check (see below).  Might be interesting to figure out why
-- that is:
-- ap/ (η {τ} {p}) (v , av) =
--   (((+ 0) , (p , id⇔)) , tt) , (id⇔ , ((+ 0) , (p , id⇔)))
-- ap/ ε (v , av) = tt , refl

postulate
  _⇔?_ : {τ : FT} → (τ ⟷ τ) → (τ ⟷ τ) → Bool

ap/ : {T : FT/} → State T → Dir × State T
ap/ (Enter (lift p) (v , _) C) = Fwd , Exit (lift p) (ap p v , refl) C 
ap/ (Enter (η p) (tt , av) C) =
   Fwd , Exit (η p) (((perm (+ 1) p idr◎r) , tt) , (id⇔ , (perm (+ 1) p idr◎r))) C
ap/ (Enter (ε p) (((perm i q α) , tt) , (β , (perm j r γ))) C) =
  if (q ⇔? r)
  then Fwd , Exit (ε p) (tt , refl) C
  else Bck , Enter (ε p) (((perm i q α) , tt) , (β , (perm j r γ))) C
ap/ (Enter unite₊l/ (inj₁ () , av) C) 
ap/ (Enter unite₊l/ (inj₂ v , av) C) = Fwd , Exit unite₊l/ (v , av) C
ap/ (Enter uniti₊l/ (v , av) C) = Fwd , Exit uniti₊l/ (inj₂ v , av) C
ap/ (Enter unite₊r/ (inj₁ v , av) C) = Fwd , Exit unite₊r/ (v , av) C
ap/ (Enter unite₊r/ (inj₂ () , av) C)
ap/ (Enter uniti₊r/ (v , av) C) = Fwd , Exit uniti₊r/ (inj₁ v , av) C
ap/ (Enter swap₊/ (inj₁ v , av) C) = Fwd , Exit swap₊/ (inj₂ v , av) C
ap/ (Enter swap₊/ (inj₂ v , av) C) = Fwd , Exit swap₊/ (inj₁ v , av) C
ap/ (Enter assocl₊/ (inj₁ v , av) C) = Fwd , Exit assocl₊/ (inj₁ (inj₁ v) , av) C
ap/ (Enter assocl₊/ (inj₂ (inj₁ v) , av) C) = Fwd , Exit assocl₊/ (inj₁ (inj₂ v) , av) C
ap/ (Enter assocl₊/ (inj₂ (inj₂ v) , av) C) = Fwd , Exit assocl₊/ (inj₂ v , av) C
ap/ (Enter assocr₊/ (inj₁ (inj₁ v) , av) C) = Fwd , Exit assocr₊/ (inj₁ v , av) C
ap/ (Enter assocr₊/ (inj₁ (inj₂ v) , av) C) = Fwd , Exit assocr₊/ (inj₂ (inj₁ v) , av) C
ap/ (Enter assocr₊/ (inj₂ v , av) C) = Fwd , Exit assocr₊/ (inj₂ (inj₂ v) , av) C
ap/ (Enter unite⋆l/ ((tt , v) , (_ , av)) C) = Fwd , Exit unite⋆l/ (v , av) C
ap/ (Enter uniti⋆l/ (v , av) C) = Fwd , Exit uniti⋆l/ ((tt , v) , (refl , av)) C
ap/ (Enter unite⋆r/ ((v , tt) , (av , att)) C) = Fwd , Exit unite⋆r/ (v , av) C
ap/ (Enter uniti⋆r/ (v , av) C) = Fwd , Exit uniti⋆r/ ((v , tt) , (av , refl)) C
ap/ (Enter swap⋆/ ((v₁ , v₂) , (av₁ , av₂)) C) = Fwd , Exit swap⋆/ ((v₂ , v₁) , (av₂ , av₁)) C
ap/ (Enter assocl⋆/ ((v₁ , (v₂ , v₃)) , ((av₁ , (av₂ , av₃)))) C) =
  Fwd , Exit assocl⋆/ (((v₁ , v₂) , v₃) , ((av₁ , av₂) , av₃)) C
ap/ (Enter assocr⋆/ (((v₁ , v₂) , v₃) , ((av₁ , av₂) , av₃)) C) =
  Fwd , Exit assocr⋆/ ((v₁ , (v₂ , v₃)) , ((av₁ , (av₂ , av₃)))) C
ap/ (Enter absorbr/ ((v , _) , (av , _)) C) = Fwd , Exit absorbr/ (v , av) C
ap/ (Enter absorbl/ ((_ , v) , (_ , av)) C) = Fwd , Exit absorbl/ (v , av) C
ap/ (Enter factorzr/ (() , _) C) 
ap/ (Enter factorzl/ (() , _) C)
ap/ (Enter dist/ ((inj₁ v₁ , v₃) , (av₁ , av₃)) C) =
  Fwd , Exit dist/ (inj₁ (v₁ , v₃) , (av₁ , av₃)) C
ap/ (Enter dist/ ((inj₂ v₂ , v₃) , (av₂ , av₃)) C) =
  Fwd , Exit dist/ (inj₂ (v₂ , v₃) , (av₂ , av₃)) C
ap/ (Enter factor/ (inj₁ (v₁ , v₃) , av) C) =
  Fwd , Exit factor/ ((inj₁ v₁ , v₃) , av) C
ap/ (Enter factor/ (inj₂ (v₂ , v₃) , av) C) =
  Fwd , Exit factor/ ((inj₂ v₂ , v₃) , av) C
ap/ (Enter distl/ ((v₃ , inj₁ v₁) , (av₃ , av₁)) C) =
  Fwd , Exit distl/ (inj₁ (v₃ , v₁) , (av₃ , av₁)) C
ap/ (Enter distl/ ((v₃ , inj₂ v₂) , (av₃ , av₂)) C) =
  Fwd , Exit distl/ (inj₂ (v₃ , v₂) , (av₃ , av₂)) C
ap/ (Enter factorl/ (inj₁ (v₃ , v₁) , av) C) =
  Fwd , Exit factorl/ ((v₃ , inj₁ v₁) , av) C
ap/ (Enter factorl/ (inj₂ (v₃ , v₂) , av) C) =
  Fwd , Exit factorl/ ((v₃ , inj₂ v₂) , av) C
ap/ (Enter id⇿ v C) = Fwd , Exit id⇿ v C
ap/ (Enter (P₁ ◎/ P₂) v C) = Fwd , Enter P₁ v (Fst C P₂)
ap/ (Enter (P₁ ⊕/ P₂) (inj₁ v₁ , av) C) = Fwd , Enter P₁ (v₁ , av) (L+ C P₂) 
ap/ (Enter (P₁ ⊕/ P₂) (inj₂ v₂ , av) C) = Fwd , Enter P₂ (v₂ , av) (R+ P₁ C) 
ap/ (Enter (P₁ ⊗/ P₂) ((v₁ , v₂) , (av₁ , av₂)) C) =
  Fwd , Enter P₁ (v₁ , av₁) (L× C P₂ (v₂ , av₂))
ap/ (Exit P v Empty) = Done , Exit P v Empty
ap/ (Exit P₁ v (Fst C P₂)) = Fwd , Enter P₂ v (Snd P₁ C) 
ap/ (Exit P₂ v₂ (Snd P₁ C)) = Fwd , Exit (P₁ ◎/ P₂) v₂ C 
ap/ (Exit P₁ v₁ (L× C P₂ v₂)) = Fwd , Enter P₂ v₂ (R× P₁ v₁ C) 
ap/ (Exit P₂ (v₂ , av₂) (R× P₁ (v₁ , av₁) C)) =
  Fwd , Exit (P₁ ⊗/ P₂) (((v₁ , v₂) , (av₁ , av₂))) C 
ap/ (Exit P₁ (v₁ , av) (L+ C P₂)) = Fwd , Exit (P₁ ⊕/ P₂) (inj₁ v₁ , av) C  
ap/ (Exit P₂ (v₂ , av) (R+ P₁ C)) = Fwd , Exit (P₁ ⊕/ P₂) (inj₂ v₂ , av) C 

ap⁻¹/ : {T : FT/} → State T → Dir × State T
ap⁻¹/ (Exit (lift p) (v , _) C) = Bck , Enter (lift p) (ap⁻¹ p v , refl) C 
ap⁻¹/ (Exit (η p) (((perm i q α) , tt) , (β , (perm j r γ))) C) =
  if (q ⇔? r)
  then Bck , Enter (η p) (tt , refl) C
  else Fwd , Exit (η p)
         (((perm (ℤsuc i) (p ◎ q) (trans⇔ (id⇔ ⊡ α) (
             trans⇔ (idr◎r ⊡ id⇔) (2! (lower {p = p} (+ 1) i))))) , tt) , (id⇔ ,
           (perm (ℤsuc j) (p ◎ r) (trans⇔ (id⇔ ⊡ γ)
             (trans⇔ (idr◎r ⊡ id⇔) (2! (lower {p = p} (+ 1) j))))))) C
ap⁻¹/ (Exit (ε p) (tt , _) C) =
  Bck , Enter (ε p) ((((perm (+ 1) p idr◎r) , tt)) , (id⇔ , (perm (+ 1) p idr◎r))) C

ap⁻¹/ (Exit uniti₊l/ (inj₁ () , av) C) 
ap⁻¹/ (Exit uniti₊l/ (inj₂ v , av) C) = Bck , Enter uniti₊l/ (v , av) C
ap⁻¹/ (Exit unite₊l/ (v , av) C) = Bck , Enter unite₊l/ (inj₂ v , av) C
ap⁻¹/ (Exit uniti₊r/ (inj₁ v , av) C) = Bck , Enter uniti₊r/ (v , av) C
ap⁻¹/ (Exit uniti₊r/ (inj₂ () , av) C)
ap⁻¹/ (Exit unite₊r/ (v , av) C) = Bck , Enter unite₊r/ (inj₁ v , av) C
ap⁻¹/ (Exit swap₊/ (inj₁ v , av) C) = Bck , Enter swap₊/ (inj₂ v , av) C
ap⁻¹/ (Exit swap₊/ (inj₂ v , av) C) = Bck , Enter swap₊/ (inj₁ v , av) C
ap⁻¹/ (Exit assocr₊/ (inj₁ v , av) C) = Bck , Enter assocr₊/ (inj₁ (inj₁ v) , av) C
ap⁻¹/ (Exit assocr₊/ (inj₂ (inj₁ v) , av) C) = Bck , Enter assocr₊/ (inj₁ (inj₂ v) , av) C
ap⁻¹/ (Exit assocr₊/ (inj₂ (inj₂ v) , av) C) = Bck , Enter assocr₊/ (inj₂ v , av) C
ap⁻¹/ (Exit assocl₊/ (inj₁ (inj₁ v) , av) C) = Bck , Enter assocl₊/ (inj₁ v , av) C
ap⁻¹/ (Exit assocl₊/ (inj₁ (inj₂ v) , av) C) = Bck , Enter assocl₊/ (inj₂ (inj₁ v) , av) C
ap⁻¹/ (Exit assocl₊/ (inj₂ v , av) C) = Bck , Enter assocl₊/ (inj₂ (inj₂ v) , av) C
ap⁻¹/ (Exit uniti⋆l/ ((tt , v) , (_ , av)) C) = Bck , Enter uniti⋆l/ (v , av) C
ap⁻¹/ (Exit unite⋆l/ (v , av) C) = Bck , Enter unite⋆l/ ((tt , v) , (refl , av)) C
ap⁻¹/ (Exit uniti⋆r/ ((v , tt) , (av , att)) C) = Bck , Enter uniti⋆r/ (v , av) C
ap⁻¹/ (Exit unite⋆r/ (v , av) C) = Bck , Enter unite⋆r/ ((v , tt) , (av , refl)) C
ap⁻¹/ (Exit swap⋆/ ((v₁ , v₂) , (av₁ , av₂)) C) = Bck , Enter swap⋆/ ((v₂ , v₁) , (av₂ , av₁)) C
ap⁻¹/ (Exit assocr⋆/ ((v₁ , (v₂ , v₃)) , ((av₁ , (av₂ , av₃)))) C) =
  Bck , Enter assocr⋆/ (((v₁ , v₂) , v₃) , ((av₁ , av₂) , av₃)) C
ap⁻¹/ (Exit assocl⋆/ (((v₁ , v₂) , v₃) , ((av₁ , av₂) , av₃)) C) =
  Bck , Enter assocl⋆/ ((v₁ , (v₂ , v₃)) , ((av₁ , (av₂ , av₃)))) C
ap⁻¹/ (Exit factorzl/ ((v , _) , (av , _)) C) = Bck , Enter factorzl/ (v , av) C
ap⁻¹/ (Exit factorzr/ ((_ , v) , (_ , av)) C) = Bck , Enter factorzr/ (v , av) C
ap⁻¹/ (Exit absorbl/ (() , _) C) 
ap⁻¹/ (Exit absorbr/ (() , _) C)
ap⁻¹/ (Exit factor/ ((inj₁ v₁ , v₃) , (av₁ , av₃)) C) =
  Bck , Enter factor/ (inj₁ (v₁ , v₃) , (av₁ , av₃)) C
ap⁻¹/ (Exit factor/ ((inj₂ v₂ , v₃) , (av₂ , av₃)) C) =
  Bck , Enter factor/ (inj₂ (v₂ , v₃) , (av₂ , av₃)) C
ap⁻¹/ (Exit dist/ (inj₁ (v₁ , v₃) , av) C) =
  Bck , Enter dist/ ((inj₁ v₁ , v₃) , av) C
ap⁻¹/ (Exit dist/ (inj₂ (v₂ , v₃) , av) C) =
  Bck , Enter dist/ ((inj₂ v₂ , v₃) , av) C
ap⁻¹/ (Exit factorl/ ((v₃ , inj₁ v₁) , (av₃ , av₁)) C) =
  Bck , Enter factorl/ (inj₁ (v₃ , v₁) , (av₃ , av₁)) C
ap⁻¹/ (Exit factorl/ ((v₃ , inj₂ v₂) , (av₃ , av₂)) C) =
  Bck , Enter factorl/ (inj₂ (v₃ , v₂) , (av₃ , av₂)) C
ap⁻¹/ (Exit distl/ (inj₁ (v₃ , v₁) , av) C) =
  Bck , Enter distl/ ((v₃ , inj₁ v₁) , av) C
ap⁻¹/ (Exit distl/ (inj₂ (v₃ , v₂) , av) C) =
  Bck , Enter distl/ ((v₃ , inj₂ v₂) , av) C
ap⁻¹/ (Exit id⇿ v C) = Bck , Enter id⇿ v C
ap⁻¹/ (Exit (P₁ ◎/ P₂) v C) = Bck , Exit P₂ v (Snd P₁ C)
ap⁻¹/ (Exit (P₁ ⊕/ P₂) (inj₁ v₁ , av) C) = Bck , Exit P₁ (v₁ , av) (L+ C P₂) 
ap⁻¹/ (Exit (P₁ ⊕/ P₂) (inj₂ v₂ , av) C) = Bck , Exit P₂ (v₂ , av) (R+ P₁ C) 
ap⁻¹/ (Exit (P₁ ⊗/ P₂) ((v₁ , v₂) , (av₁ , av₂)) C) =
  Bck , Exit P₂ (v₂ , av₂) (R× P₁ (v₁ , av₁) C)
ap⁻¹/ (Enter P v Empty) = Done , Enter P v Empty
ap⁻¹/ (Enter P₁ v (Fst C P₂)) = Bck , Enter (P₁ ◎/ P₂) v C 
ap⁻¹/ (Enter P₂ v₂ (Snd P₁ C)) = Bck , Exit P₁ v₂ (Fst C P₂)
ap⁻¹/ (Enter P₁ (v₁ , av₁) (L× C P₂ (v₂ , av₂))) =
  Bck , Enter (P₁ ⊗/ P₂) (((v₁ , v₂) , (av₁ , av₂))) C 
ap⁻¹/ (Enter P₂ (v₂ , av₂) (R× P₁ (v₁ , av₁) C)) =
  Bck , Exit P₁ (v₁ , av₁) (L× C P₂ (v₂ , av₂))
ap⁻¹/ (Enter P₁ (v₁ , av) (L+ C P₂)) = Bck , Enter (P₁ ⊕/ P₂) (inj₁ v₁ , av) C  
ap⁻¹/ (Enter P₂ (v₂ , av) (R+ P₁ C)) = Bck , Enter (P₁ ⊕/ P₂) (inj₂ v₂ , av) C 

{-# NON_TERMINATING #-}
mutual 
  loopFwd : {T : FT/} → State T → V T
  loopFwd s with ap/ s
  ... | Fwd , s' = loopFwd s'
  ... | Bck , s' = loopBck s'
  ... | Done , Exit _ v Empty = v
  ... | Done , _ = {!!}

  loopBck : {T : FT/} → State T → V T
  loopBck s with ap⁻¹/ s
  ... | Bck , s' = loopBck s'
  ... | Fwd , s' = loopFwd s'
  ... | Done , _ = {!!}

-- Credit card example

cc : # NOT ⇿ # NOT
cc = uniti⋆l/ ◎/
     (((η NOT) ⊗/ id⇿) ◎/
     ((assocr⋆/ ◎/
     ((id⇿ ⊗/ swap⋆/) ◎/
     ((id⇿ ⊗/ (ε NOT)) ◎/
     unite⋆r/)))))

\end{code}

%%%%%%%
\subsection{Pragmatics}

We have a way to generate programs at run time from eta: it would be
nice to have a way to execute these programs. 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

