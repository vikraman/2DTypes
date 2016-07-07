\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module opsem where

open import Data.Empty using (⊥)
open import Level using () renaming (zero to l0; suc to lsuc)
open import Universe using (Universe)
open import Data.Bool
open import Data.Sum hiding ([_,_])
open import Data.Product hiding (<_,_>)
open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc)
open import Data.Integer
  using (ℤ; +_; -[1+_])
  renaming (-_ to ℤ-; suc to ℤsuc; _+_ to _ℤ+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; subst; cong; sym; cong₂)-- ; inspect; [_])
open import Categories.Groupoid.Sum using () renaming (Sum to GSum)
open import Categories.Groupoid.Product using () renaming (Product to GProduct)
open import Function using (case_of_)

open import pifrac

get-q : {t : U} {p : t ⟷ t} → Val (# p) → t ⟷ t
get-q (comb i) = Iter.q i

get-iter : {t : U} {p : t ⟷ t} → Val (# p) → Iter p
get-iter (comb i) = i

get// : {t : U} {p q : t ⟷ t} → Val (p // q) → p ÷ q
get// (tangr x) = x

get\\ : {t : U} {p q : t ⟷ t} → Val (q \\ p) → p ÷ q
get\\ (tangl x) = x

π₁ : {s t : U} → Val (s ⊗ t) → Val s
π₁ [ x , _ ] = x
π₂ : {s t : U} → Val (s ⊗ t) → Val t
π₂ [ _ , y ] = y

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{$\Pi^/$: Operational Semantics} 

The operational semantics for all the primitive combinators is a
simple transliteration of Fig.~\ref{opsem}. We omit the
straightforward implementation of \AgdaFunction{prim} and its inverse
below:

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{
\begin{code}
prim :    {τ₁ τ₂ : U} → (Prim⟷ τ₁ τ₂) → Val τ₁ → Val τ₂
prim⁻¹ :  {τ₁ τ₂ : U} → (Prim⟷ τ₁ τ₂) → Val τ₂ → Val τ₁
\end{code}}}}
\AgdaHide{
\begin{code}
prim = {!!} 
prim⁻¹ = {!!} 
\end{code}
}

The interesting combinators operationally are the unit/counit
combinators $\eta$ and $\epsilon$ and the synchronization
combinators. Their semantics is defined in the following pair of
mutually recursive interpreters:

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{
\begin{code}
mutual
  𝓐𝓹 : {τ₁ τ₂ : U} → (τ₁ ⟷ τ₂) → Val τ₁ → Val τ₂
  𝓐𝓹 (Prim c) v = prim c v
  𝓐𝓹 id⟷ v = v
  𝓐𝓹 (c₁ ◎ c₂) v = 𝓐𝓹 c₂ (𝓐𝓹 c₁ v)
  𝓐𝓹 (c₁ ⊕ c₂) (inl v) = inl (𝓐𝓹 c₁ v)
  𝓐𝓹 (c₁ ⊕ c₂) (inr v) = inr (𝓐𝓹 c₂ v)
  𝓐𝓹 (c₁ ⊗ c₂) [ v , w ] = [ 𝓐𝓹 c₁ v , 𝓐𝓹 c₂ w ]
  𝓐𝓹 (η- c) ⋆ = tangl (c÷c c)
  𝓐𝓹 (η+ c) ⋆ = tangr (c÷c c)
  𝓐𝓹 (ε+ c) (tangr v) = ⋆
  𝓐𝓹 (ε- c) (tangl v) = ⋆
  𝓐𝓹 synchr⋆ [ tangr w , v ] = [ v , tangl w ]
  𝓐𝓹 synchl⋆ [ v , tangl w ] = [ tangr w , v ]

  𝓐𝓹⁻¹ : {τ₁ τ₂ : U} → (τ₁ ⟷ τ₂) → Val τ₂ → Val τ₁
  𝓐𝓹⁻¹ (Prim c) v = prim⁻¹ c v
  𝓐𝓹⁻¹ id⟷ v = v
  𝓐𝓹⁻¹ (c₁ ◎ c₂) v = 𝓐𝓹⁻¹ c₁ (𝓐𝓹⁻¹ c₂ v)
  𝓐𝓹⁻¹ (c₁ ⊕ c₂) (inl v) = inl (𝓐𝓹⁻¹ c₁ v)
  𝓐𝓹⁻¹ (c₁ ⊕ c₂) (inr v) = inr (𝓐𝓹⁻¹ c₂ v)
  𝓐𝓹⁻¹ (c₁ ⊗ c₂) [ v , w ] = [ (𝓐𝓹⁻¹ c₁ v) , (𝓐𝓹⁻¹ c₂ w) ]
  𝓐𝓹⁻¹ (η- c) (tangl v) = ⋆
  𝓐𝓹⁻¹ (η+ c) (tangr v) = ⋆
  𝓐𝓹⁻¹ (ε+ c) ⋆ = tangr (c÷c c)
  𝓐𝓹⁻¹ (ε- c) ⋆ = tangl (c÷c c)
  𝓐𝓹⁻¹ synchr⋆ [ v , tangl w ] = [ tangr w , v ]
  𝓐𝓹⁻¹ synchl⋆ [ tangr w , v ] = [ v , tangl w ]
\end{code}}}}

The unit combinators $\eta$ simply generate unit tangles, and since
unit tangles are equivalent to the identity they can be freely
eliminated by the counit combinators $\epsilon$. The two
synchronization operations exchange the tangled product with an
iterate. The two interpreters satisfy several properties described
below: First they are congruences for the equivalence $≈$ on values.
We can further prove that both are \emph{reversible}.  Furthermore, we
can show two further coherence conditions: first, that the reverse
interpreter give equivalent results to the forward interpreter applied
to a reverse combinator, and second, that two equivalent combinators
(as given by a 2-combinator) will evaluate to equivalent values.

\newcommand{\textpi}{$\pi$}

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{
\begin{code}
mutual
  inj-eq : {s t : U} (v₁ v₂ : Val (s ⊕ t)) → Set
  inj-eq (inl v) (inl w) = v ≈ w
  inj-eq (inl v) (inr w) = ⊥
  inj-eq (inr v) (inl w) = ⊥
  inj-eq (inr v) (inr w) = v ≈ w
  
  data _≈_ : {t : U} → Val t → Val t → Set where
    ⋆≈  :     {e f : Val 𝟙} → e ≈ f
    #p≈ :     ∀ {t} {p : t ⟷ t} {p^i p^j : Val (# p)} →
              get-q p^i ⇔ get-q p^j → p^i ≈ p^j
    [,]≈ :    {s t : U} {v₁ v₂ : Val (s ⊗ t)} →
              π₁ v₁ ≈ π₁ v₂ → π₂ v₁ ≈ π₂ v₂ → v₁ ≈ v₂
    inj≈ :    {s t : U} → {v₁ v₂ : Val (s ⊕ t)} →
              inj-eq v₁ v₂ → v₁ ≈ v₂
    tangr≈ :  {τ : U} {p q : τ ⟷ τ} → {f g : Val (p // q)} →
              (∀ {x : Iter p} {y : Iter q} →
              Σ.proj₁ (get// f x y) ⇔ Σ.proj₁ (get// g x y)) → f ≈ g
    tangl≈ :  {τ : U} {q p : τ ⟷ τ} → {f g : Val (q \\ p)} →
              (∀ {x : Iter p} {y : Iter q} →
              Σ.proj₁ (get\\ f x y) ⇔ Σ.proj₁ (get\\ g x y)) → f ≈ g

cong≈ :  {τ₁ τ₂ : U} → (c : τ₁ ⟷ τ₂) {v w : Val τ₁} → 
         v ≈ w → 𝓐𝓹 c v ≈ 𝓐𝓹 c w
cong≈ = {!!} -- omitted

fwd◎bwd≈id :  {τ₁ τ₂ : U} → (c : τ₁ ⟷ τ₂) → (v : Val τ₂) → 
              𝓐𝓹 c (𝓐𝓹⁻¹ c v) ≈ v
fwd◎bwd≈id = {!!} -- omitted

bwd-coherence :  {τ₁ τ₂ : U} → (c : τ₁ ⟷ τ₂) → (v : Val τ₂) → 
                 𝓐𝓹⁻¹ c v ≈ 𝓐𝓹 (! c) v
bwd-coherence = {!!} -- omitted

fwd-2-coherence :  {τ₁ τ₂ : U} → (c₁ c₂ : τ₁ ⟷ τ₂) →
                   (α : c₁ ⇔ c₂) → 
                   (v : Val τ₁) → 𝓐𝓹 c₁ v ≈ 𝓐𝓹 c₂ v
fwd-2-coherence = {!!} -- omitted
\end{code}}}}

%%%%%%%
\subsection{Examples} 

We implement two examples that are similar to the credit card example
from the introduction.

\AgdaHide{
\begin{code}
refl≈ : ∀ {t} {v w : Val t} → v ≡ w → v ≈ w
refl≈ = {!!} 
\end{code}}

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{
\begin{code}
-- coherence of unit and counit

zig-zag : ∀ {t : U} {c : t ⟷ t} → # c ⟷ # c
zig-zag {_} {c} =
  Prim uniti⋆l ◎ η+ c ⊗ id⟷ ◎
  synchr⋆ ◎ (id⟷ ⊗ ε- c) ◎ Prim unite⋆r

zig-zag-prop : {t : U} {c : t ⟷ t} (v : Val (# c)) → 𝓐𝓹 zig-zag v ≈ v
zig-zag-prop (comb x) = refl≈ refl

-- credit card like 

BOOL : U
BOOL = 𝟙 ⊕ 𝟙

NOT : BOOL ⟷ BOOL
NOT = Prim swap₊

cc : # NOT ⟷ # NOT
cc = Prim uniti⋆l ◎
     (((η+ NOT) ⊗ id⟷) ◎ 
     ((synchr⋆ ◎ 
     ((id⟷ ⊗ (ε- NOT)) )))) ◎
     Prim unite⋆r

i₀ i₁ : Iter NOT
i₀ = < + 0 , id⟷ , id⇔ >
i₁ = < + 1 , NOT , idr◎r >

v₀ v₁ : Val (# NOT)
v₀ = comb i₀
v₁ = comb i₁

cc₁ cc₂ : Val (# NOT)
cc₁ = 𝓐𝓹 cc v₀ -- evaluates to v₀, on the nose
cc₂ = 𝓐𝓹 cc v₁ -- evaluates to v₁, on the nose
\end{code}}}}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

