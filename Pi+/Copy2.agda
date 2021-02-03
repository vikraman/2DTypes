{-# OPTIONS --rewriting --without-K #-}

module Pi+.Copy2 where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.Univalence
open import lib.PathGroupoid
open import lib.PathOver
open import lib.types.Fin
open import lib.types.List
open import lib.types.Sigma
open import lib.types.Coproduct
open import lib.types.Unit
open import lib.types.Nat

open import Pi+.Extra

infix 2 Σ-syntax

Σ-syntax : (A : Type₀) (B : A → Type₀) → Type₀
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

private
  variable
    k : ℕ

fzero : Fin (S k)
fzero = (0 , O<S _)

-- Conversion back to ℕ is trivial...
toℕ : Fin k → ℕ
toℕ = fst

⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
⟨_⟩ = Fin-S

S⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
S⟨ k , kltn ⟩ = S k , <-ap-S kltn


_≤^_ : {m : ℕ} -> Fin m -> Fin m -> Type₀
k ≤^ n = (k .fst) < S (n .fst)

<-down : {n k : ℕ} -> (S n < k) -> (n < k)
<-down p = <-cancel-S (ltSR p)

-- ... and injective.
toℕ-injective : ∀{fj fk : Fin k} → toℕ fj == toℕ fk → fj == fk
toℕ-injective {fj = fj} {fk} p = pair= p TODO

S⟨⟩-inj : {n : ℕ} -> {fj fk : Fin n} → S⟨ fj ⟩ == S⟨ fk ⟩ → fj == fk
S⟨⟩-inj = toℕ-injective ∘ ℕ-S-is-inj _ _ ∘ ap toℕ


fsplit
  : ∀(fj : Fin (S k))
  → (fzero == fj) ⊔ (Σ[ fk ∈ Fin k ] S⟨ fk ⟩ == fj)
fsplit (0 , k<sn) = inl (toℕ-injective idp)
fsplit (S k , k<sn) = inr ((k , <-cancel-S k<sn) , toℕ-injective idp)

punchOutprim : ∀ {m} {i j : Fin (S m)} → (¬ (i == j)) → Fin m
punchOutprim {_} {i} {j} p with fsplit i | fsplit j
punchOutprim {_} {i} {j} p | inl x | inl y = ⊥-elim (p (! x ∙ y))
punchOutprim {_} {i} {j} p | inl x | inr (y , yp) = y
punchOutprim {S m} {i} {j} p | inr x | inl y = fzero
punchOutprim {S m} {i} {j} p | inr (x , xp) | inr (y , yp) = S⟨ punchOutprim {i = x} {j = y} (λ q → p (! xp ∙ ap S⟨_⟩ q ∙ yp)) ⟩

punchOut-inj : ∀ {m} {i j k : Fin (S m)} (i≢j : ¬ (i == j)) (i≢k : ¬ (i == k)) → punchOutprim i≢j == punchOutprim i≢k → j == k
punchOut-inj {_} {i} {j} {k} i≢j i≢k p with fsplit i | fsplit j | fsplit k
punchOut-inj {O} {i} {j} {k} i≢j i≢k p | inl ip | inl jp | _ = ⊥-elim (i≢j (! ip ∙ jp))
punchOut-inj {S m} {i} {j} {k} i≢j i≢k p | inl ip | inl jp | kp = ⊥-elim (i≢j (! ip ∙ jp))
punchOut-inj {S m} {i} {j} {k} i≢j i≢k p | inl ip | inr _ | inl kp = ⊥-elim (i≢k (! ip ∙ kp))
punchOut-inj {S m} {i} {j} {k} i≢j i≢k p | inl ip | inr (jp , jpp) | inr (kp , kpp) = ! jpp ∙ ap S⟨_⟩ p ∙ kpp
punchOut-inj {S m} {i} {j} {k} i≢j i≢k p | inr ip | inl jp | inl kp = ! jp ∙ kp
punchOut-inj {S m} {i} {j} {k} i≢j i≢k p | inr (ip , ipp) | inr (jp , jpp) | inr (kp , kpp) = 
  let lemma-j = λ p → i≢j (! ipp ∙ ap S⟨_⟩ p ∙ jpp)
      lemma-k = λ p → i≢k (! ipp ∙ ap S⟨_⟩ p ∙ kpp) 
      rec = punchOut-inj {j = jp} {k = kp} lemma-j lemma-k (S⟨⟩-inj p)
  in  ! jpp ∙ ap S⟨_⟩ rec ∙ kpp

private
  variable
    n : ℕ

FinExcept : (i : Fin n) → Type₀
FinExcept i = Σ[ j ∈ Fin _ ] ¬ (i == j)

isSetFinExcept : {i : Fin n} → is-set (FinExcept i)
isSetFinExcept = {!   !}

fsuc : _
fsuc = S⟨_⟩

fsuc-inj : _
fsuc-inj = S⟨⟩-inj

fsucExc : {i : Fin n} → FinExcept i → FinExcept (fsuc i)
fsucExc {i = i} j = fsuc (fst j) , snd j ∘ fsuc-inj

toFinExc : {i : Fin n} → FinExcept i → Fin n
toFinExc = fst

toFinExc-injective : {i : Fin n} → {j k : FinExcept i} → toFinExc j == toFinExc k → j == k
toFinExc-injective = {!   !}

toℕExc : {i : Fin n} → FinExcept i → ℕ
toℕExc = toℕ ∘ toFinExc

toℕExc-injective : {i : Fin n} → {j k : FinExcept i} → toℕExc j == toℕExc k → j == k
toℕExc-injective = toFinExc-injective ∘ toℕ-injective

projectionEquiv : {i : Fin n} → (Unit ⊔ FinExcept i) ≃ Fin n
projectionEquiv {n = n} {i = i} = equiv f g f-g g-f
    where
      f : _
      f (inl _) = i
      f (inr m) = fst m
      g : _
      g m with (Fin-has-dec-eq i m)
      ... | (inl _) = inl tt
      ... | (inr n) = inr (m , n)
      f-g : _
      f-g m with Fin-has-dec-eq i m
      ... | (inl p) = p
      ... | (inr _) = toℕ-injective idp
      g-f : _
      g-f (inl tt) with Fin-has-dec-eq i i
      ... | (inl _) = idp
      ... | (inr ¬ii) with (¬ii idp)
      ... | ()
      g-f (inr m) with Fin-has-dec-eq i (fst m)
      ... | (inr _) = ap inr (toℕExc-injective idp)
      ... | (inl p) with (snd m p)
      ... | ()

punchOut : (i : Fin (S n)) → FinExcept i → Fin n
punchOut i ¬i = punchOutprim (snd ¬i)

punchOut-injective : (i : Fin (S n)) → ∀ j k → punchOut i j == punchOut i k → j == k
punchOut-injective i j k = toFinExc-injective ∘ punchOut-inj (snd j) (snd k)

fznotfs : ∀ {m : ℕ} {k : Fin m} → ¬ (fzero == fsuc k)
fznotfs {m} p = {!   !}
  where
    F : Fin (S m) → Type₀
    F (O , _) = Unit
    F (S _ , _) = ⊥

¬Fin0 : ¬ (Fin 0)
¬Fin0 ()


punchIn : (i : Fin (S n)) → Fin n → FinExcept i
punchIn {_} i j with fsplit i
...             | inl iz = fsuc j , fznotfs ∘ (iz ∙_)
punchIn {n} i j | inr (i′ , is) with n
...                 | O = ⊥-elim (¬Fin0 j)
...                 | S n′ with fsplit j
...                     | inl jz = fzero , fznotfs ∘ ! ∘ (is ∙_)
...                     | inr (j′ , _) =
                            let (k , ¬k≡i′) = punchIn i′ j′
                            in fsuc k , ¬k≡i′ ∘ fsuc-inj ∘ (is ∙_)

punchOut∘In :(i : Fin (S n)) → ∀ j → punchOut i (punchIn i j) == j
punchOut∘In {_} i j with fsplit i
...                 | inl iz = toℕ-injective idp
punchOut∘In {n} i j | inr (i′ , _) with n
...                     | O  with (¬Fin0 j)
...                         | ()
punchOut∘In {n} i j | inr (i′ , _) | S n′ with fsplit j
...                         | inl jz = toℕ-injective (ap toℕ jz)
...                         | inr (j′ , prfj) =
                              -- the following uses a definitional equality of punchIn but I don't see
                              -- how to sidestep this while using with-abstractions
                              fsuc (punchOut i′ _)               =⟨ ap (λ j → fsuc (punchOut i′ j)) (toℕExc-injective idp) ⟩
                              fsuc (punchOut i′ (punchIn i′ j′)) =⟨ ap fsuc (punchOut∘In i′ j′) ⟩
                              fsuc j′                            =⟨ toℕ-injective (ap toℕ prfj) ⟩
                              j                                  =∎

isEquivPunchOut : {i : Fin (S n)} → is-equiv (punchOut i)
isEquivPunchOut {i = i} = {!   !} -- isEmbedding×isSurjection→isEquiv (isEmbPunchOut , isSurPunchOut) where
  -- isEmbPunchOut : isEmbedding (punchOut i)
  -- isEmbPunchOut = injEmbedding isSetFinExcept isSetFin λ {_} {_} → punchOut-injective i _ _
  -- isSurPunchOut : isSurjection (punchOut i)
  -- isSurPunchOut b = ∣ _ , punchOut∘In i b ∣

punchOutEquiv : {i : Fin (S n)} → FinExcept i ≃ Fin n
punchOutEquiv = _ , isEquivPunchOut

infixr 4 _∷_
data LehmerCode : (n : ℕ) → Type₀ where
  [] : LehmerCode O
  _∷_ : ∀ {n} → Fin (S n) → LehmerCode n → LehmerCode (S n)

isContrLehmerZero : is-contr (LehmerCode 0)
isContrLehmerZero = ?

lehmerSucEquiv : Fin (S n) × LehmerCode n ≃ LehmerCode (S n)
lehmerSucEquiv = equiv (λ (e , c) → e ∷ c)
                                 (λ { (e ∷ c) → (e , c) })
                                 (λ { (e ∷ c) → idp })
                                 (λ (e , c) → idp)

equivFun : ∀ {A B : Type₀} → A ≃ B → A → B
equivFun e = fst e

-- lehmerEquiv : (Fin n ≃ Fin n) ≃ LehmerCode n
-- lehmerEquiv {zero} = ?
-- lehmerEquiv {S n} =
--   (Fin (S n) ≃ Fin (S n))                              ≃⟨ isoToEquiv i ⟩
--   (Σ[ k ∈ Fin (S n) ] (FinExcept fzero ≃ FinExcept k)) ≃⟨ Σ-cong-equiv-snd ii ⟩
--   (Fin (S n) × (Fin n ≃ Fin n))                        ≃⟨ Σ-cong-equiv-snd (λ _ → lehmerEquiv) ⟩
--   (Fin (S n) × LehmerCode n)                           ≃⟨ lehmerSucEquiv ⟩
--   LehmerCode (S n) ■ where
--     equivIn : (f : Fin (S n) ≃ Fin (S n))
--             → FinExcept fzero ≃ FinExcept (equivFun f fzero)
--     equivIn f =
--       FinExcept fzero
--         ≃⟨ Σ-cong-equiv-snd (λ _ → preCompEquiv (invEquiv (congEquiv f))) ⟩
--       (Σ[ x ∈ Fin (S n) ] ¬ ffun fzero ≡ ffun x)
--         ≃⟨ Σ-cong-equiv-fst f ⟩
--       FinExcept (ffun fzero)
--         ■ where ffun = equivFun f

-- --    equivInChar : ∀ {f} x → fst (equivFun (equivIn f) x) ≡ equivFun f (fst x)
-- --    equivInChar x = idp

--     equivOut : ∀ {k} → FinExcept (fzero {k = n}) ≃ FinExcept k
--              → Fin (S n) ≃ Fin (S n)
--     equivOut {k = k} f =
--       Fin (S n)
--         ≃⟨ invEquiv projectionEquiv ⟩
--       Unit ⊎ FinExcept fzero
--         ≃⟨ isoToEquiv (Sum.sumIso idIso (equivToIso f)) ⟩
--       Unit ⊎ FinExcept k
--         ≃⟨ projectionEquiv ⟩
--       Fin (S n)
--         ■

--     equivOutChar : ∀ {k} {f} (x : FinExcept fzero) → equivFun (equivOut {k = k} f) (fst x) ≡ fst (equivFun f x)
--     equivOutChar {f = f} x with discreteFin fzero (fst x)
--     ... | (yes y) = ⊥.rec (x .snd y)
--     ... | (no n) = cong (λ x′ → fst (equivFun f x′)) (toℕExc-injective idp)

--     i : Iso (Fin (S n) ≃ Fin (S n))
--             (Σ[ k ∈ Fin (S n) ] (FinExcept (fzero {k = n}) ≃ FinExcept k))
--     Iso.fun i f = equivFun f fzero , equivIn f
--     Iso.inv i (k , f) = equivOut f
--     Iso.rightInv i (k , f) = ΣPathP (idp , equivEq (funExt λ x →
--        toℕExc-injective (cong toℕ (equivOutChar {f = f} x))))
--     Iso.leftInv i f = equivEq (funExt goal) where
--       goal : ∀ x → equivFun (equivOut (equivIn f)) x ≡ equivFun f x
--       goal x = case fsplit x return (λ _ → equivFun (equivOut (equivIn f)) x ≡ equivFun f x) of λ
--         { (inl xz) → subst (λ x → equivFun (equivOut (equivIn f)) x ≡ equivFun f x) xz idp
--         ; (inr (_ , xn)) → equivOutChar {f = equivIn f} (x , fznotfs ∘ (_∙ sym xn))
--         }

--     ii : ∀ k → (FinExcept fzero ≃ FinExcept k) ≃ (Fin n ≃ Fin n)
--     ii k = (FinExcept fzero ≃ FinExcept k) ≃⟨ cong≃ (λ R → FinExcept fzero ≃ R) punchOutEquiv ⟩
--            (FinExcept fzero ≃ Fin n)       ≃⟨ cong≃ (λ L → L ≃ Fin n) punchOutEquiv  ⟩
--            (Fin n ≃ Fin n)                 ■
