{-# OPTIONS --rewriting --without-K #-}

module Pi+.Lehmer.FinHelpers where

open import HoTT hiding (⟨_⟩)

open import Pi+.Common.FinHelpers public

infix 2 Σ-syntax

Σ-syntax : (A : Type₀) (B : A → Type₀) → Type₀
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

private
  variable
    k : ℕ

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

instance
    isSetFinExcept : {i : Fin n} → is-set (FinExcept i)
    isSetFinExcept = Σ-level Fin-is-set (λ x → raise-level (S ⟨-2⟩) (Π-level (λ p → Empty-is-prop)))

fsuc : _
fsuc = S⟨_⟩

fsuc-inj : _
fsuc-inj = S⟨⟩-inj

fsucExc : {i : Fin n} → FinExcept i → FinExcept (fsuc i)
fsucExc {i = i} j = fsuc (fst j) , snd j ∘ fsuc-inj

toFinExc : {i : Fin n} → FinExcept i → Fin n
toFinExc = fst

toFinExc-injective : {i : Fin n} → {j k : FinExcept i} → toFinExc j == toFinExc k → j == k
toFinExc-injective {i = i} {(j , jpp)} {(k , kpp)} t = pair= t prop-has-all-paths-↓

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
      g m with (Fin-has-dec-eq-p i m)
      ... | (inl _) = inl tt
      ... | (inr n) = inr (m , n)
      f-g : _
      f-g m with Fin-has-dec-eq-p i m
      ... | (inl p) = p
      ... | (inr _) = toℕ-injective idp
      g-f : _
      g-f (inl tt) with Fin-has-dec-eq-p i i
      ... | (inl _) = idp
      ... | (inr ¬ii) with (¬ii idp)
      ... | ()
      g-f (inr m) with Fin-has-dec-eq-p i (fst m)
      ... | (inr _) = ap inr (toℕExc-injective idp)
      ... | (inl p) with (snd m p)
      ... | ()

punchOut : (i : Fin (S n)) → FinExcept i → Fin n
punchOut i ¬i = punchOutprim (snd ¬i)

punchOut-injective : (i : Fin (S n)) → ∀ j k → punchOut i j == punchOut i k → j == k
punchOut-injective i j k = toFinExc-injective ∘ punchOut-inj (snd j) (snd k)

fznotfs : ∀ {m : ℕ} {k : Fin m} → ¬ (fzero == fsuc k)
fznotfs {m} ()

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
isEquivPunchOut {i = i} = is-eq (punchOut i) (punchIn i) (punchOut∘In i) λ a →
    let q = punchOut∘In i (punchOut i a)
    in  punchOut-injective i _ _ q

punchOutEquiv : {i : Fin (S n)} → FinExcept i ≃ Fin n
punchOutEquiv = _ , isEquivPunchOut


equivFun : ∀ {A B : Type₀} → A ≃ B → A → B
equivFun e = fst e

congEquiv : {A B : Type₀} {x y : A} (e : A ≃ B) → (x == y) ≃ (equivFun e x == equivFun e y)
congEquiv e = ap-equiv e _ _

equivEq : {A B : Type₀} {e f : A ≃ B} → (h : e .fst == f .fst) → e == f
equivEq {e = e} {f = f} h = pair= h prop-has-all-paths-↓

preCompEquiv : {A B C : Type₀} -> (e : A ≃ B) → (B → C) ≃ (A → C)
preCompEquiv e = equiv f g f-g g-f
  where
  f : _
  f x = λ z → x (fst e z)
  g : _
  g x b = x (<– e b)
  f-g : _
  f-g x = λ= (λ a → ap x (<–-inv-l e a))
  g-f : _
  g-f x = λ= (λ a → ap x (<–-inv-r e a))

Σ-cong-equiv-fst : {A A' : Type₀} {B : A' -> Type₀} (e : A ≃ A') → (Σ A (B ∘ (equivFun e))) ≃ (Σ A' B)
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

equivIn : {n : ℕ} -> (f : Fin (S n) ≃ Fin (S n))
        → FinExcept fzero ≃ FinExcept (equivFun f fzero)
equivIn {n} f =
  FinExcept fzero
    ≃⟨ Σ-cong-equiv-snd (λ _ → preCompEquiv (_⁻¹ (congEquiv f))) ⟩
  (Σ[ x ∈ Fin (S n) ] ¬ (ffun fzero == ffun x))
    ≃⟨ Σ-cong-equiv-fst f ⟩
  FinExcept (ffun fzero)
    ≃∎ 
    where ffun = equivFun f

equivOut : ∀ {n : ℕ} {k : Fin (S n)} → FinExcept (fzero {k = n}) ≃ FinExcept k → Fin (S n) ≃ Fin (S n)
equivOut {n} {k = k} f =
  Fin (S n)
    ≃⟨ _⁻¹ projectionEquiv ⟩
  Unit ⊔ FinExcept fzero
    ≃⟨ Coprod-≃-l f ⟩
  Unit ⊔ FinExcept k
    ≃⟨ projectionEquiv ⟩
  Fin (S n)
    ≃∎

equivOutChar : ∀ {n : ℕ} {k : Fin (S n)} {f : FinExcept (fzero {k = n}) ≃ FinExcept k} (x : FinExcept fzero) → equivFun (equivOut {k = k} f) (fst x) == fst (equivFun f x)
equivOutChar {n} {k = k} {f = f} x with Fin-has-dec-eq-p fzero (fst x)
... | (inr p) = 
  let ll = toℕExc-injective idp
      ff = (λ x′ → fst (equivFun f x′))
  in  ap ff ll
... | (inl y) with (x .snd y)
... | ()

i : {n : ℕ} -> (Fin (S n) ≃ Fin (S n)) ≃ (Σ[ k ∈ Fin (S n) ] (FinExcept (fzero {k = n}) ≃ FinExcept k))
i {n} = equiv ff g f-g g-f 
  where
    ff : _
    ff f  = equivFun f fzero , equivIn f
    g : _
    g (k , f) = equivOut f
    f-g : _
    f-g (k , f) = pair= idp (equivEq (λ= λ x → toℕExc-injective (ap toℕ (equivOutChar {f = f} x))))
    g-f : _
    g-f f = equivEq (λ= goal) where
      goal : ∀ x → equivFun (equivOut (equivIn f)) x == equivFun f x
      goal x with fsplit x
      ... | (inr (_ , xn)) = equivOutChar {f = equivIn f} (x , fznotfs ∘ (_∙ ! xn))
      ... | (inl xz) = transport (λ x → equivFun (equivOut (equivIn f)) x == equivFun f x) xz idp
      

ii : ∀ {n : ℕ} (k : Fin (S n)) → (FinExcept fzero ≃ FinExcept k) ≃ (Fin n ≃ Fin n)
ii {n} k = (FinExcept fzero ≃ FinExcept k)   ≃⟨ {!  cong≃ (λ R → (FinExcept (fzero {k = n})) ≃ R) punchOutEquiv !} ⟩ -- 
        (FinExcept fzero ≃ Fin n)         ≃⟨ {!  cong≃ (λ L → L ≃ Fin n) punchOutEquiv  !} ⟩ -- 
        (Fin n ≃ Fin n)                   ≃∎