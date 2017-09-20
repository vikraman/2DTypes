module PiFin.Fin where

open import IntensionalTypeTheory

data Fin : ℕ → Type₀ where
  fzero : ∀ {n} → Fin (succ n)
  fsucc : ∀ {n} → Fin n → Fin (succ n)

infixr 40 _∷_

data List (A : Type₀) : ℕ → Type₀ where
  []  : List A 0
  _∷_ : ∀ {n} → A → List A n → List A (succ n)

fin-down : ∀ {A : Type₀} {n} → (Fin (succ n) → A) → Fin n → A
fin-down f x = f (fsucc x)

fin-out : ∀ {A : Type₀} {n} → (Fin n → A) → List A n
fin-out {n = zero} f = []
fin-out {n = succ n} f = f fzero ∷ fin-out (fin-down f)

fin-in : ∀ {A : Type₀} {n} → List A n → Fin n → A
fin-in (x ∷ xs) fzero = x
fin-in (x ∷ xs) (fsucc f) = fin-in xs f

fin-in-out : ∀ {n A} (f : Fin n → A) (x : Fin n) → fin-in (fin-out f) x == f x
fin-in-out {zero}   f ()
fin-in-out {succ n} f fzero = refl (f fzero)
fin-in-out {succ n} f (fsucc x) = fin-in-out (fin-down f) x

fin-up : ∀ {A : Type₀} {n} → (Fin n → A) → A → Fin (succ n) → A
fin-up f a fzero = a
fin-up f a (fsucc x) = f x

fin-out-in : ∀ {A n} (xs : List A n) → fin-out (fin-in xs) == xs
fin-out-in [] = refl []
fin-out-in (x ∷ xs) = ap (_∷_ x) (fin-out-in xs)

open import FunctionExtensionality

fin-list-equiv : ∀ {A n} → (Fin n → A) ≃ List A n
fin-list-equiv = fin-out , qinv-is-equiv (fin-in , (funext ∘ fin-in-out) , fin-out-in)

data _≤_ : ℕ → ℕ → Type₀ where
  z≤n : ∀ {n} → zero ≤ n
  s≤n : ∀ {m n} → m ≤ n → succ m ≤ succ n

≤-refl : ∀ n → n ≤ n
≤-refl zero = z≤n
≤-refl (succ n) = s≤n (≤-refl n)

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans {zero} z≤n q = z≤n
≤-trans {succ m} (s≤n p) (s≤n q) = s≤n (≤-trans p q)

≤-succ : ∀ m → m ≤ succ m
≤-succ zero = z≤n
≤-succ (succ n) = s≤n (≤-succ n)

_<_ : ℕ → ℕ → Type₀
m < n = succ m ≤ n

_>_ : ℕ → ℕ → Type₀
m > n = n < m

data Dec {p} (P : Type p) : Type p where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

Decidable : ∀ {p r} {P : Type p} (R : P → P → Type r) → Type (p ⊔ r)
Decidable R = ∀ x y → Dec (R x y)

_≤?_ : Decidable _≤_
zero ≤? n = yes z≤n
succ m ≤? zero = no (λ ())
succ m ≤? succ n with m ≤? n
... | yes m≤n = yes (s≤n m≤n)
... | no  m≰n = no (m≰n ∘ (λ { (s≤n m≤n) → m≤n }))

compare : ∀ m n → (m < n) + (m == n) + (m > n)
compare zero zero = i₂ (i₁ (refl zero))
compare zero (succ n) = i₁ (s≤n z≤n)
compare (succ m) zero = i₂ (i₂ (s≤n z≤n))
compare (succ m) (succ n) with compare m n
... | i₁ m<n = i₁ (s≤n m<n)
... | i₂ (i₁ m=n) = i₂ (i₁ (ap succ m=n))
... | i₂ (i₂ n>m) = i₂ (i₂ (s≤n n>m))

fin-zero-n : ∀ n → ¬ (Fin 0 ≃ Fin (succ n))
fin-zero-n n (f , g , _) with g fzero
... | ()

open import EmbeddingsInUniverse
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

fin-el-equiv : ∀ {n m} → Fin n ≃ Fin m → El n ≃ El m
fin-el-equiv eq = (!e el-fin-equiv) ● eq ● el-fin-equiv

open import Univalence

fin-equiv : ∀ {n m} → Fin n ≃ Fin m → n == m
fin-equiv {n} {m} eq = PathsInℕ.reflect n m (ua (fin-el-equiv eq))
