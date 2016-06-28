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

_≡#_ : {τ : U} {p : τ ⟷ τ} {p^i p^j q^i q^j : Iter p} → p^i ⇔# p^j → q^i ⇔# q^j → Set
(mor#p ⟪ p_q , _ ⟫ ⟪ p_r , _ ⟫ _) ≡# (mor#p ⟪ q_q , _ ⟫ ⟪ q_r , _ ⟫ _) = Equiv p_q q_q p_r q_r

id#p : {τ : U} {p : τ ⟷ τ} {p^i : Iter p} → p^i ⇔# p^i
id#p {_} {p} { < i , q , α > }  =
  mor#p ⟪ p , id⇔ ⟫ ⟪ p , id⇔ ⟫ (id⇔ ⊡ α ● assoc1g i ● (2! α) ⊡ id⇔)

----------------------------------------------------------------------------
-- for #1/p

record _⇔1/#_ {τ : U} {p : τ ⟷ τ} (p^i : Sing p) (p^j : Sing p) : Set where
  constructor mor1/#p
  field
    q : Iter p
    r : Iter p
    χ : Iter.q q ◎ Sing.p' p^i ⇔ Sing.p' p^j ◎ Iter.q r

