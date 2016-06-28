module 2D.ProgMorphisms where

open import 2D.Types

open import 2D.Sing
open import 2D.Iter
open import 2D.Power

----------------------------------------------------------------------------
-- Generally useful lemmas

-- we can always exchange a Sing and an Iter
swapSI : {τ : U} {p : τ ⟷ τ} (r : Sing p) (p^i : Iter p) →
  Sing.p' r ◎ Iter.q p^i ⇔ Iter.q p^i ◎ Sing.p' r
swapSI ⟪ p' , eq ⟫ < k , q , α > = eq ⊡ α ● assoc1g k ● 2! α ⊡ 2! eq

----------------------------------------------------------------------------
-- For generic equivalences

-- (no need for a constructor, as we should never see the insides of this
--  outside of this file.)
record Equiv {τ : U} (p q r s : τ ⟷ τ) : Set where
  field
    p⇔q : p ⇔ q
    r⇔q : r ⇔ q
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
refl# {m = mor#p ⟪ p₁ , α ⟫ ⟪ p₂ , β ⟫ _} = record { p⇔q = id⇔ ; r⇔q = β ● 2! α ; r⇔s = id⇔ }

-- basic morphisms and properties
id#p : {τ : U} {p : τ ⟷ τ} {p^i : Iter p} → p^i ⇔# p^i
id#p {_} {p} { < i , q , α > }  =
  mor#p ⟪ p , id⇔ ⟫ ⟪ p , id⇔ ⟫ (id⇔ ⊡ α ● assoc1g i ● (2! α) ⊡ id⇔)

sym⇔#p : {τ : U} {p : τ ⟷ τ} {p^i q^j : Iter p} → p^i ⇔# q^j → q^j ⇔# p^i
sym⇔#p {p^i = p^i} {q^j} (mor#p q r χ) = mor#p r q (swapSI r q^j ● 2! χ ● swapSI q p^i)

sym#p : {τ : U} {p : τ ⟷ τ} {p q : Iter p} {m₁ m₂ : p ⇔# q} → m₁ ≡# m₂ → m₂ ≡# m₁
sym#p record { p⇔q = p⇔q ; r⇔q = r⇔q ; r⇔s = r⇔s } =
  record { p⇔q = 2! p⇔q ; r⇔q = 2! r⇔s ● r⇔q ● 2! p⇔q ; r⇔s = 2! r⇔s }

trans#p : {τ : U} {p : τ ⟷ τ} {p q : Iter p} {i j k : p ⇔# q} →
  i ≡# j → j ≡# k → i ≡# k
trans#p record { p⇔q = p⇔q ; r⇔q = r⇔q ; r⇔s = r⇔s }
        record { p⇔q = p⇔q₁ ; r⇔q = r⇔q₁ ; r⇔s = r⇔s₁ } = record
  { p⇔q = p⇔q ● p⇔q₁
  ; r⇔q = r⇔q ● p⇔q₁ -- note how r⇔q₁ is not used
  ; r⇔s = r⇔s ● r⇔s₁
  }

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
  ; r⇔q = 2! eq
  ; r⇔s = 2! eq₁
  }

id#pʳ : {τ : U} {p : τ ⟷ τ} {a b : Iter p} {m : a ⇔# b} → (m ∘# id#p) ≡# m
id#pʳ {p = p} {m = mor#p ⟪ p' , eq ⟫ ⟪ p'' , eq₁ ⟫ χ} = record
  { p⇔q = id⇔ ; r⇔q = eq₁ ● 2! eq ; r⇔s = id⇔ }

assoc# : {τ : U} {p : τ ⟷ τ} {a b c d : Iter p} {f : a ⇔# b} {g : b ⇔# c} {h : c ⇔# d} →
  ((h ∘# g) ∘# f) ≡# (h ∘# (g ∘# f))
assoc# {f = mor#p q r χ} {mor#p q₁ r₁ χ₁} {mor#p q₂ r₂ χ₂} = record
  { p⇔q = id⇔ ; r⇔q = sing⇔ r₂ q₂ ; r⇔s = id⇔ }

-- because composition is forgetful, second argument is irrelevant!
∘#-resp-≡# : {τ : U} {p : τ ⟷ τ} {a b c : Iter p} {f h : b ⇔# c} {g i : a ⇔# b} →
  f ≡# h → g ≡# i → (f ∘# g) ≡# (h ∘# i)
∘#-resp-≡# eq _ = eq

isoˡ#p : {τ : U} {p : τ ⟷ τ} {a b : Iter p} { eq : a ⇔# b} → ((sym⇔#p eq) ∘# eq) ≡# id#p {p^i = b}
isoˡ#p {eq = mor#p q r _} = record { p⇔q = Sing.eq r ; r⇔q = Sing.eq q ; r⇔s = Sing.eq q }

isoʳ#p : {τ : U} {p : τ ⟷ τ} {a b : Iter p} { eq : a ⇔# b} → (eq ∘# (sym⇔#p eq)) ≡# id#p {p^i = b}
isoʳ#p {eq = mor#p q r _} = record { p⇔q = Sing.eq q ; r⇔q = Sing.eq r ; r⇔s = Sing.eq r }

----------------------------------------------------------------------------
-- for #1/p

record _⇔1/#_ {τ : U} {p : τ ⟷ τ} (p^i : Sing p) (p^j : Sing p) : Set where
  constructor mor1/#p
  field
    q : Iter p
    r : Iter p
    χ : Iter.q q ◎ Sing.p' p^i ⇔ Sing.p' p^j ◎ Iter.q r

