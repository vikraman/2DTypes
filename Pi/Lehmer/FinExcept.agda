{-# OPTIONS --rewriting --without-K --exact-split --overlapping-instances #-}

module Pi.Lehmer.FinExcept where

open import HoTT hiding (⟨_⟩)

open import Pi.Common.FinHelpers public
open import Pi.Common.Misc

private
  variable
    k : ℕ

fsplit
  : ∀(fj : Fin (S k))
  → (fzero == fj) ⊔ Σ (Fin k) (λ fk → S⟨ fk ⟩ == fj)
fsplit (0 , k<sn) = inl (toℕ-inj idp)
fsplit (S k , k<sn) = inr ((k , <-cancel-S k<sn) , toℕ-inj idp)

punchOutprim : ∀ {m} {i j : Fin (S m)} → (¬ (i == j)) → Fin m
punchOutprim {_} {i} {j} p with fsplit i | fsplit j
... | inl x | inl y = ⊥-rec (p (! x ∙ y))
... | inl x | inr (y , yp) = y
punchOutprim {S m} {i} {j} p | inr x | inl y = fzero
punchOutprim {S m} {i} {j} p | inr (x , xp) | inr (y , yp) = S⟨ punchOutprim {i = x} {j = y} (λ q → p (! xp ∙ ap S⟨_⟩ q ∙ yp)) ⟩

-- not really an injection
abstract
  punchOutprim-inj : ∀ {m} {i j k : Fin (S m)} (i≢j : ¬ (i == j)) (i≢k : ¬ (i == k)) → punchOutprim i≢j == punchOutprim i≢k → j == k
  punchOutprim-inj {_} {i} {j} {k} i≢j i≢k p with fsplit i | fsplit j | fsplit k
  punchOutprim-inj {O} {i} {j} {k} i≢j i≢k p | inl ip | inl jp | _ = ⊥-rec (i≢j (! ip ∙ jp))
  punchOutprim-inj {S m} {i} {j} {k} i≢j i≢k p | inl ip | inl jp | kp = ⊥-rec (i≢j (! ip ∙ jp))
  punchOutprim-inj {S m} {i} {j} {k} i≢j i≢k p | inl ip | inr _ | inl kp = ⊥-rec (i≢k (! ip ∙ kp))
  punchOutprim-inj {S m} {i} {j} {k} i≢j i≢k p | inl ip | inr (jp , jpp) | inr (kp , kpp) = ! jpp ∙ ap S⟨_⟩ p ∙ kpp
  punchOutprim-inj {S m} {i} {j} {k} i≢j i≢k p | inr ip | inl jp | inl kp = ! jp ∙ kp
  punchOutprim-inj {S m} {i} {j} {k} i≢j i≢k p | inr (ip , ipp) | inr (jp , jpp) | inr (kp , kpp) =
    let lemma-j : ¬ (ip == jp)
        lemma-j p = i≢j (! ipp ∙ ap S⟨_⟩ p ∙ jpp)
        lemma-k : ¬ (ip == kp)
        lemma-k p = i≢k (! ipp ∙ ap S⟨_⟩ p ∙ kpp)
        rec = punchOutprim-inj {j = jp} {k = kp} lemma-j lemma-k (S⟨⟩-inj p)
    in  ! jpp ∙ ap S⟨_⟩ rec ∙ kpp

private
  variable
    n : ℕ

FinExcept : (i : Fin n) → Type₀
FinExcept {n} i = Σ (Fin n) (λ j → ¬ (i == j))

FinExcept-is-set : {i : Fin n} → is-set (FinExcept i)
FinExcept-is-set = ⟨⟩

fsuc : _
fsuc = S⟨_⟩

fsuc-inj : _
fsuc-inj = S⟨⟩-inj

fsucExc : {i : Fin n} → FinExcept i → FinExcept (fsuc i)
fsucExc {i = i} j = fsuc (fst j) , snd j ∘ fsuc-inj

toFinExc : {i : Fin n} → FinExcept i → Fin n
toFinExc = fst

module _ {i : Fin n} {j k : FinExcept i} where
  abstract
    toFinExc-inj : toFinExc j == toFinExc k → j == k
    toFinExc-inj t = pair= t prop-has-all-paths-↓

    ap-toFinExc-equiv : is-equiv (ap toFinExc {x = j} {y = k})
    ap-toFinExc-equiv =
      is-eq (ap toFinExc) toFinExc-inj
            (λ _ → prop-has-all-paths _ _) (λ _ → prop-has-all-paths _ _)

toℕExc : {i : Fin n} → FinExcept i → ℕ
toℕExc = toℕ ∘ toFinExc

module _ {i : Fin n} {j k : FinExcept i} where
  abstract
    toℕExc-inj : toℕExc j == toℕExc k → j == k
    toℕExc-inj = toFinExc-inj ∘ toℕ-inj

    ap-toℕExc-equiv : is-equiv (ap toℕExc {x = j} {y = k})
    ap-toℕExc-equiv =
      is-eq (ap toℕExc) toℕExc-inj
            (λ _ → prop-has-all-paths _ _) (λ _ → prop-has-all-paths _ _)

projectionEquiv : {i : Fin n} → (Unit ⊔ FinExcept i) ≃ Fin n
projectionEquiv {n = n} {i = i} = equiv f g f-g g-f
    where
      f : _
      f (inl _) = i
      f (inr m) = fst m
      g : _
      g m with (Fin-has-dec-eq-p i m)
      ... | (inl _) = inl tt
      ... | (inr n) = inr (m , n)
      f-g : _
      f-g m with Fin-has-dec-eq-p i m
      ... | (inl p) = p
      ... | (inr _) = toℕ-inj idp
      g-f : _
      g-f (inl tt) with Fin-has-dec-eq-p i i
      ... | (inl _) = idp
      ... | (inr ¬ii) with (¬ii idp)
      ... | ()
      g-f (inr m) with Fin-has-dec-eq-p i (fst m)
      ... | (inr _) = ap inr (toℕExc-inj idp)
      ... | (inl p) with (snd m p)
      ... | ()

punchOut : (i : Fin (S n)) → FinExcept i → Fin n
punchOut i ¬i = punchOutprim (¬i .snd)

module _ (i : Fin (S n)) {j k : FinExcept i} where
  abstract
    punchOut-inj : punchOut i j == punchOut i k → j == k
    punchOut-inj = toFinExc-inj ∘ punchOutprim-inj (j .snd) (k .snd)

    ap-punchOut-equiv : is-equiv (ap (punchOut i) {x = j} {y = k})
    ap-punchOut-equiv =
      is-eq (ap (punchOut i)) punchOut-inj
            (λ _ → prop-has-all-paths _ _)
            (λ _ → prop-has-all-paths _ _)

fznotfs : ∀ {m : ℕ} {k : Fin m} → ¬ (fzero == fsuc k)
fznotfs {m} ()

¬Fin0 : ¬ (Fin 0)
¬Fin0 ()

punchIn : (i : Fin (S n)) → Fin n → FinExcept i
punchIn {_} i j with fsplit i
...             | inl iz = fsuc j , fznotfs ∘ (iz ∙_)
punchIn {n} i j | inr (i′ , is) with n
...                 | O = ⊥-rec (¬Fin0 j)
...                 | S n′ with fsplit j
...                     | inl jz = fzero , fznotfs ∘ ! ∘ (is ∙_)
...                     | inr (j′ , _) =
                            let (k , ¬k≡i′) = punchIn i′ j′
                            in fsuc k , ¬k≡i′ ∘ fsuc-inj ∘ (is ∙_)

punchOut∘In :(i : Fin (S n)) → ∀ j → punchOut i (punchIn i j) == j
punchOut∘In {_} i j with fsplit i
...                 | inl iz = toℕ-inj idp
punchOut∘In {n} i j | inr (i′ , _) with n
...                     | O  = ⊥-rec (¬Fin0 j)
punchOut∘In {n} i j | inr (i′ , _) | S n′ with fsplit j
...                         | inl jz = toℕ-inj (ap toℕ jz)
...                         | inr (j′ , prfj) =
                              -- the following uses a definitional equality of punchIn but I don't see
                              -- how to sidestep this while using with-abstractions
                              fsuc (punchOut i′ _)               =⟨ ap (fsuc ∘ (punchOut i′)) (toℕExc-inj idp) ⟩
                              fsuc (punchOut i′ (punchIn i′ j′)) =⟨ ap fsuc (punchOut∘In i′ j′) ⟩
                              fsuc j′                            =⟨ toℕ-inj (ap toℕ prfj) ⟩
                              j                                  =∎

punchOutEquiv : {i : Fin (S n)} → FinExcept i ≃ Fin n
punchOutEquiv {n} {i} =
  equiv (punchOut i) (punchIn i)
        (punchOut∘In i)
        (punchOut-inj i ∘ punchOut∘In i ∘ punchOut i)

abstract
  preCompEquiv : {A B C : Type₀} -> (e : A ≃ B) → (A → C) ≃ (B → C)
  preCompEquiv e =
    equiv (_∘ <– e) (_∘ (–> e))
          (λ f → λ= (ap f ∘ (<–-inv-r e)))
          (λ f → λ= (ap f ∘ (<–-inv-l e)))

Σ-cong-equiv-fst : {A A' : Type₀} {B : A' -> Type₀} (e : A ≃ A') → (Σ A (B ∘ (–> e))) ≃ (Σ A' B)
Σ-cong-equiv-fst {B = B} e = _ , (Σ-isemap-l B (snd e))

Σ-cong-equiv-snd : {A : Type₀} {B B' : A -> Type₀} -> (∀ a → B a ≃ B' a) → Σ A B ≃ Σ A B'
Σ-cong-equiv-snd x = (λ (a , b) → a , (–> (x a) b)) , (Σ-isemap-r (λ a → snd (x a)))

Coprod-≃-l : {A B C : Type₀} -> (A ≃ B) -> (C ⊔ A) ≃ (C ⊔ B)
Coprod-≃-l e = equiv f g f-g g-f
    where
    f : _
    f (inl x) = inl x
    f (inr x) = inr (–> e x)
    g : _
    g (inl x) = inl x
    g (inr x) = inr (<– e x)
    f-g : _
    f-g (inl x) = idp
    f-g (inr x) = ap inr (<–-inv-r e x)
    g-f : _
    g-f (inl x) = idp
    g-f (inr x) = ap inr (<–-inv-l e x)

equivIn : {n : ℕ}
        → (f : Fin (S n) ≃ Fin (S n))
        → FinExcept fzero ≃ FinExcept (–> f fzero)
equivIn {n} f =
  FinExcept fzero
    ≃⟨ Σ-cong-equiv-snd (preCompEquiv ∘ (ap-equiv f fzero)) ⟩
  Σ (Fin (S n)) (λ x → ¬ (ffun fzero == ffun x))
    ≃⟨ Σ-cong-equiv-fst f ⟩
  FinExcept (ffun fzero)
    ≃∎
    where ffun = –> f

equivOut : ∀ {n : ℕ} {k : Fin (S n)}
         → FinExcept (fzero {k = n}) ≃ FinExcept k
         → Fin (S n) ≃ Fin (S n)
equivOut {n} {k = k} f =
  Fin (S n)
    ≃⟨ projectionEquiv ⁻¹ ⟩
  Unit ⊔ FinExcept fzero
    ≃⟨ Coprod-≃-l f ⟩
  Unit ⊔ FinExcept k
    ≃⟨ projectionEquiv ⟩
  Fin (S n)
    ≃∎

equivOut-β : ∀ {n : ℕ} {k : Fin (S n)} {f : FinExcept (fzero {k = n}) ≃ FinExcept k} (x : FinExcept fzero) → –> (equivOut {k = k} f) (x .fst) == fst (–> f x)
equivOut-β {n} {k = k} {f = f} x with Fin-has-dec-eq-p fzero (x .fst)
... | (inr p) = ap (fst ∘ –> f) (toℕExc-inj idp)
... | (inl y) = ⊥-rec (x .snd y)

i : {n : ℕ} → (Fin (S n) ≃ Fin (S n)) ≃ Σ (Fin (S n)) (λ k → (FinExcept (fzero {k = n}) ≃ FinExcept k))
i {n} = equiv ff g f-g g-f
  where
    ff : _
    ff f  = –> f fzero , equivIn f
    g : _
    g (k , f) = equivOut f
    f-g : _
    f-g (k , f) = pair= idp (e= (toℕExc-inj ∘ ap toℕ ∘ equivOut-β {f = f}))
    g-f : _
    g-f f = e= goal where
      goal : ∀ x → –> (equivOut (equivIn f)) x == –> f x
      goal x with fsplit x
      ... | (inr (_ , xn)) = equivOut-β {f = equivIn f} (x , fznotfs ∘ (_∙ ! xn))
      ... | (inl xz) = transport (λ x → –> (equivOut (equivIn f)) x == –> f x) xz idp

ii : ∀ {n : ℕ} (k : Fin (S n)) → (FinExcept fzero ≃ FinExcept k) ≃ (Fin n ≃ Fin n)
ii {n} k = (FinExcept fzero ≃ FinExcept k)   ≃⟨ cong≃ punchOutEquiv ⟩
           (FinExcept fzero ≃ Fin n)         ≃⟨ !≃ (cong≃ punchOutEquiv) ⟩
           (Fin n ≃ Fin n)                   ≃∎
