module PiFin.Fin where

open import UnivalentTypeTheory

data Fin : ℕ → Type₀ where
  fzero : ∀ {n} → Fin (succ n)
  fsucc : ∀ {n} → Fin n → Fin (succ n)

fin-zero-n : ∀ n → ¬ (Fin 0 ≃ Fin (succ n))
fin-zero-n n (f , g , _) with g fzero
... | ()

fsucc-inj : {n : ℕ} → (f g : Fin n) → fsucc f == fsucc g → f == g
fsucc-inj f .f (refl .(fsucc f)) = refl f

fin-has-dec-eq : (n : ℕ) → has-dec-eq (Fin n)
fin-has-dec-eq zero ()
fin-has-dec-eq (succ n) fzero fzero = i₁ (refl fzero)
fin-has-dec-eq (succ n) fzero (fsucc g) = i₂ (λ ())
fin-has-dec-eq (succ n) (fsucc f) fzero = i₂ (λ ())
fin-has-dec-eq (succ n) (fsucc f) (fsucc g) with fin-has-dec-eq n f g
... | i₁ f=g = i₁ (ap fsucc f=g)
... | i₂ f≠g = i₂ (λ p → f≠g (fsucc-inj f g p))

fin-is-set : {n : ℕ} → is-set (Fin n)
fin-is-set {n} = hedberg (Fin n) (fin-has-dec-eq n)

open import PiFin.EmbeddingsInUniverse
open UnivalentUniverseOfFiniteTypes

el-in : ∀ {n} → Fin n → El n
el-in {.(succ _)} fzero = i₁ 0₁
el-in {.(succ _)} (fsucc f) = i₂ (el-in f)

el-out : ∀ {n} → El n → Fin n
el-out {zero} ()
el-out {succ n} (i₁ e) = fzero
el-out {succ n} (i₂ e) = fsucc (el-out e)

el-in-out : ∀ {n} (e : El n) → el-in (el-out e) == e
el-in-out {zero} ()
el-in-out {succ n} (i₁ 0₁) = refl (i₁ 0₁)
el-in-out {succ n} (i₂ e) = ap i₂ (el-in-out e)

el-out-in : ∀ {n} (f : Fin n) → el-out (el-in f) == f
el-out-in {.(succ _)} fzero = refl fzero
el-out-in {.(succ _)} (fsucc f) = ap fsucc (el-out-in f)

el-fin-equiv : ∀ {n} → El n ≃ Fin n
el-fin-equiv = el-out , qinv-is-equiv (el-in , el-in-out , el-out-in)

module _ {n m} where
  fin-equiv-el-equiv : (Fin n ≃ Fin m) ≃ (El n ≃ El m)
  fin-equiv-el-equiv = f , qinv-is-equiv (g , η , ε)
    where f : Fin n ≃ Fin m → El n ≃ El m
          f eq = !e el-fin-equiv ● eq ● el-fin-equiv
          g : El n ≃ El m → Fin n ≃ Fin m
          g eq = el-fin-equiv ● eq ● !e el-fin-equiv
          η : g ∘ f ∼ id
          η (f , f-is-equiv) = eqv= (funext λ x → el-out-in (f (el-out (el-in x))) ◾ ap f (el-out-in x))
          ε : f ∘ g ∼ id
          ε (f , f-is-equiv) = eqv= (funext λ x → el-in-out (f (el-in (el-out x))) ◾ ap f (el-in-out x))

  fin-equiv-el-equiv-path : (Fin n ≃ Fin m) == (El n ≃ El m)
  fin-equiv-el-equiv-path = ua fin-equiv-el-equiv

  fin-equiv-el-path : (Fin n ≃ Fin m) → (El n == El m)
  fin-equiv-el-path eq = ua (p₁ fin-equiv-el-equiv eq)

fin-equiv-el-equiv-ide : ∀ {n} → p₁ fin-equiv-el-equiv (ide (Fin n)) == ide (El n)
fin-equiv-el-equiv-ide = dpair= (funext el-in-out , is-equiv-is-prop _ _ _)

fin-equiv-el-path-ide : ∀ {n} → fin-equiv-el-path (ide (Fin n)) == refl (El n)
fin-equiv-el-path-ide {n} = ap ua fin-equiv-el-equiv-ide ◾ ua-ide (El n)

fin-equiv-out : ∀ {n m} → Fin n ≃ Fin m → n == m
fin-equiv-out {n} {m} eq = PathsInℕ.reflect n m (fin-equiv-el-path eq)

-- running the equivalence instead of ua/transport
module _ {n} where
  fin-succ-equiv : Fin (succ n) ≃ 𝟙 + Fin n
  fin-succ-equiv =
    f₂ ∘ f₁ , qinv-is-equiv (g₁ ∘ g₂ , (λ x → ap g₁ (η₂ (f₁ x)) ◾ η₁ x)
                                     , (λ x → ap f₂ (ε₁ (g₂ x)) ◾ ε₂ x))
    where f₁ : Fin (succ n) → 𝟙 + El n
          f₁ = el-in
          f₂ : 𝟙 + El n → 𝟙 + Fin n
          f₂ (i₁ x) = i₁ x
          f₂ (i₂ x) = i₂ (el-out x)
          g₁ : 𝟙 + El n → Fin (succ n)
          g₁ (i₁ x) = fzero
          g₁ (i₂ x) = fsucc (el-out x)
          g₂ : 𝟙 + Fin n → 𝟙 + El n
          g₂ (i₁ x) = i₁ x
          g₂ (i₂ x) = i₂ (el-in x)
          η₁ : g₁ ∘ f₁ ∼ id
          η₁ fzero = refl fzero
          η₁ (fsucc x) = ap fsucc (el-out-in x)
          η₂ : g₂ ∘ f₂ ∼ id
          η₂ (i₁ x) = refl (i₁ x)
          η₂ (i₂ x) = ap i₂ (el-in-out x)
          ε₁ : f₁ ∘ g₁ ∼ id
          ε₁ (i₁ 0₁) = refl (i₁ 0₁)
          ε₁ (i₂ x) = ap i₂ (el-in-out x)
          ε₂ : f₂ ∘ g₂ ∼ id
          ε₂ (i₁ x) = refl (i₁ x)
          ε₂ (i₂ x) = ap i₂ (el-out-in x)

  fin-succ-path : Fin (succ n) == 𝟙 + Fin n
  fin-succ-path = ua fin-succ-equiv

reflect-refl : ∀ {n} → PathsInℕ.reflect n n (refl (El n)) == refl n
reflect-refl {zero} = refl (refl 0)
reflect-refl {succ n} = ap (λ p → ap succ (PathsInℕ.reflect n n p)) (ua-ide (El n))
                      ◾ ap (ap succ) reflect-refl

fin-equiv-out-id : ∀ {n} → fin-equiv-out (ide (Fin n)) == refl n
fin-equiv-out-id {n} = ap (PathsInℕ.reflect n n) fin-equiv-el-path-ide ◾ reflect-refl

fin-equiv-in : ∀ {n m} → m == n → Fin m ≃ Fin n
fin-equiv-in = tpt-eqv Fin

fin-equiv-retr : ∀ {n m} → is-retract (n == m) (Fin n ≃ Fin m)
fin-equiv-retr = fin-equiv-out , fin-equiv-in , ε
  where ε : ∀ {n m} → (p : n == m) → fin-equiv-out (fin-equiv-in p) == p
        ε (refl n) = fin-equiv-out-id
