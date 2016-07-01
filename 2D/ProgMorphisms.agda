{-# OPTIONS --without-K #-}

module 2D.ProgMorphisms where

open import Data.Product

open import 2D.Types
open import 2D.Sing
open import 2D.Iter
open import 2D.Power
open import 2D.Val

----------------------------------------------------------------------------
-- For generic equivalences

infix 4 _≡≈_

-- because of 'without-K', this needs to cover all cases, as we can't
-- case split on just one sub-case of ≈, so we need two auxilliaries
-- which we need to be total (because of Agda) but whose only case that
-- matters is the 1/ case.
get-a-p : ∀ {t} → Val t → Σ U (λ s → s ⟷ s)
get-a-p {𝟙} ⋆ = 𝟙 , Prim id⟷
get-a-p (inl {t} v) = t , Prim id⟷
get-a-p (inr {t} v) = t , Prim id⟷
get-a-p ([_,_] {s} {t} _ _) = s ⊗ t , Prim id⟷
get-a-p (comb {t} {p} x) = t , p
get-a-p (1/comb {t} {p} x) = t , p
get-a-p (𝟙ₚ {t} {p} _) = t , p

get-iter : ∀ {t} {p₁ p₂ : Val t} → p₁ ≈ p₂ →
  let ap = get-a-p p₁ in let s = proj₁ ap in let p = proj₂ ap in
  Iter {s} p
get-iter {_} {⋆} ⋆≈ = zeroth (proj₂ (get-a-p ⋆))
get-iter (#p≈ {_} {p} p^i p^j x) = zeroth p
get-iter (1/#p≈ q p₁ p₂ x) = q
get-iter (𝟙ₚ≈ p₁ q r x) = p₁ -- the only important case!
get-iter ([,]≈ {_} {_} {v} {_} {w} pf pf₁) = zeroth (proj₂ (get-a-p [ v , w ] ))
get-iter (inj₁≈ {_} {t₂} {v} {_} pf) = zeroth (proj₂ (get-a-p (inl {_} {t₂} v)))
get-iter (inj₂≈ {_} {_} {_} {w} pf) = zeroth (proj₂ (get-a-p (inr w)))

-- (no need for a constructor, as we should never see the insides of this
--  outside of this file.)
-- almost all cases are trivial, except for the 1/ case, at the end
data _≡≈_ : {τ : U} {p q : Val τ} (x y : p ≈ q) → Set where
  ⋆≡ : {e f : ⋆ ≈ ⋆} → e ≡≈ f
  #p≡ : ∀ {t} {p : t ⟷ t} {p^i p^j : Iter p} {e f : comb p^i ≈ comb p^j} → e ≡≈ f
  𝟙ₚ≡ :  ∀ {t} {p : t ⟷ t} {q r : Iter p} → {e f : (𝟙ₚ q) ≈ (𝟙ₚ r)} → e ≡≈ f
  [,]≡ : {s t : U} {sv₁ sv₂ : Val s} {tv₁ tv₂ : Val t}
        {e f : [ sv₁ , tv₁ ] ≈ [ sv₂ , tv₂ ]} → e ≡≈ f
  inj₁≡ : {s t : U} → {sv₁ sv₂ : Val s} {e f : inl {s} {t} sv₁ ≈ inl sv₂} → e ≡≈ f
  inj₂≡ : {s t : U} → {tv₁ tv₂ : Val t} {e f : inr {s} {t} tv₁ ≈ inr tv₂} → e ≡≈ f

  1/#p≡ : ∀ {t} {p : t ⟷ t}  {p₁ p₂ : Sing p} →
          { e f : (1/comb p₁) ≈ (1/comb p₂) } →
          Iter.q (get-iter e) ⇔ Iter.q (get-iter f) → e ≡≈ f


refl# : {τ : U} {p : τ ⟷ τ} {p q : Val τ} {eq : p ≈ q} → eq ≡≈ eq
refl# {eq = ⋆≈} = ⋆≡
refl# {eq = #p≈ p^i p^j x} = #p≡
refl# {eq = 1/#p≈ q p₁ p₂ x} = 1/#p≡ id⇔ -- only interesting case
refl# {eq = 𝟙ₚ≈ p₂ q r x} = 𝟙ₚ≡
refl# {eq = [,]≈ eq eq₁} = [,]≡
refl# {eq = inj₁≈ eq} = inj₁≡
refl# {eq = inj₂≈ eq} = inj₂≡

sym# : {τ : U} {p : τ ⟷ τ} {p q : Val τ} {l r : p ≈ q} → l ≡≈ r → r ≡≈ l
sym# ⋆≡ = ⋆≡
sym# #p≡ = #p≡
sym# 𝟙ₚ≡ = 𝟙ₚ≡
sym# [,]≡ = [,]≡
sym# inj₁≡ = inj₁≡
sym# inj₂≡ = inj₂≡
sym# (1/#p≡ x) = 1/#p≡ (2! x)

-- I am stuck on this?!?
trans# : {τ : U} {p q : Val τ} {i j k : p ≈ q} →
  i ≡≈ j → j ≡≈ k → i ≡≈ k
trans# {𝟘} () jj
trans# {𝟙} {.⋆} {.⋆} {i} {j} {k} ⋆≡ jj = ⋆≡
trans# {τ₁ ⊕ τ₂} inj₁≡ jj = inj₁≡
trans# {τ₁ ⊕ τ₂} inj₂≡ jj = inj₂≡
trans# {τ₁ ⊗ τ₂} [,]≡ jj = [,]≡
trans# {# x} #p≡ jj = #p≡
trans# {1/# x} (1/#p≡ x₁) jj = {!!}
trans# {𝟙# x} 𝟙ₚ≡ jj = 𝟙ₚ≡

{-
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

-}
