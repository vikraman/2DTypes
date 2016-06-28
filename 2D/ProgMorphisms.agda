module 2D.ProgMorphisms where

open import 2D.Types

open import 2D.Sing
open import 2D.Iter
open import 2D.Power

----------------------------------------------------------------------------
-- For generic equivalences

record Equiv {τ : U} (p q r s : τ ⟷ τ) : Set where
  field
    p⇔q : p ⇔ q
    q⇔r : q ⇔ r
    r⇔s : r ⇔ s

----------------------------------------------------------------------------
-- for #p

record _⇔#_ {τ : U} {p : τ ⟷ τ} (p^i : Iter p) (p^j : Iter p) : Set where
  constructor mor#p
  field
    q : Sing p
    r : Sing p
    χ : (Sing.p' q ◎ Iter.q p^i) ⇔ (Iter.q p^j ◎ Sing.p' r)

-- Equivalence for this case, and its properties
_≡#_ : {τ : U} {p : τ ⟷ τ} {p^i p^j q^i q^j : Iter p} → p^i ⇔# p^j → q^i ⇔# q^j → Set
(mor#p ⟪ p_q , _ ⟫ ⟪ p_r , _ ⟫ _) ≡# (mor#p ⟪ q_q , _ ⟫ ⟪ q_r , _ ⟫ _) = Equiv p_q q_q p_r q_r

refl# : {τ : U} {p : τ ⟷ τ} {p q : Iter p} {m : p ⇔# q} → m ≡# m
refl# {m = mor#p ⟪ p₁ , α ⟫ ⟪ p₂ , β ⟫ _} = record { p⇔q = id⇔ ; q⇔r = α ● 2! β ; r⇔s = id⇔ }

-- basic morphisms and properties
id#p : {τ : U} {p : τ ⟷ τ} {p^i : Iter p} → p^i ⇔# p^i
id#p {_} {p} { < i , q , α > }  =
  mor#p ⟪ p , id⇔ ⟫ ⟪ p , id⇔ ⟫ (id⇔ ⊡ α ● assoc1g i ● (2! α) ⊡ id⇔)

_∘#_ : {τ : U} {p : τ ⟷ τ} {a b c : Iter p} → b ⇔# c → a ⇔# b → a ⇔# c
_∘#_ {_} {_} { < i , a , α > } { < j , b , β > } { < k , c , γ > }
  (mor#p bc-q bc-r bc-χ) (mor#p ab-q ab-r ab-χ) =
  mor#p (bc-q ∘S ab-q) (bc-r ∘S ab-r)
    ((bc-q_eq ● 2! ab-q_eq) ⊡ id⇔ ● ab-χ ● β ⊡ ab-r_eq ● 2! (assoc1g j) ●
    2! bc-q_eq ⊡ (2! β) ● bc-χ)
  where
    open _⇔#_
    open Sing
    bc-q_eq = Sing.eq bc-q
    ab-q_eq = Sing.eq ab-q
    ab-r_eq = Sing.eq ab-r

id#pˡ : {τ : U} {p : τ ⟷ τ} {a b : Iter p} {m : a ⇔# b} → (id#p ∘# m) ≡# m
id#pˡ {p = p} {m = mor#p ⟪ p' , eq ⟫ ⟪ p'' , eq₁ ⟫ χ} = record
  { p⇔q = 2! eq
  ; q⇔r = eq
  ; r⇔s = 2! eq₁
  }

id#pʳ : {τ : U} {p : τ ⟷ τ} {a b : Iter p} {m : a ⇔# b} → (m ∘# id#p) ≡# m
id#pʳ {p = p} {m = mor#p ⟪ p' , eq ⟫ ⟪ p'' , eq₁ ⟫ χ} = record
  { p⇔q = id⇔ ; q⇔r = eq ● 2! eq₁ ; r⇔s = id⇔ }

----------------------------------------------------------------------------
-- for #1/p

record _⇔1/#_ {τ : U} {p : τ ⟷ τ} (p^i : Sing p) (p^j : Sing p) : Set where
  constructor mor1/#p
  field
    q : Iter p
    r : Iter p
    χ : Iter.q q ◎ Sing.p' p^i ⇔ Sing.p' p^j ◎ Iter.q r

