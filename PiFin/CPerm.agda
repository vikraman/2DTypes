module PiFin.CPerm where

open import Type using (Type; Type₀)
open import PiFin.Lift using (Lift; lift)
open import One
open import Paths using (_==_)
open import Functions using (_∘_; id)
open import Homotopies using (_∼_)
open import DependentSum using (_×_; _,_; p₁; p₂)
open import Coproduct using (i₁; i₂)
open import Equivalences using (_≃_)

open import NaturalNumbers

open import EmbeddingsInUniverse using (module UnivalentUniverseOfFiniteTypes)
open UnivalentUniverseOfFiniteTypes using (El)

pattern fzero   = i₁ 0₁
pattern fsucc x = i₂ x

Vec : ∀ {ℓ} (A : Type ℓ) (n : ℕ) → Type ℓ
Vec A 0        = Lift 𝟙
Vec A (succ n) = A × Vec A n

tabulate : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → (El n → A) → Vec A n
tabulate {n = 0}      f = lift 0₁
tabulate {n = succ n} f = f fzero , tabulate (f ∘ fsucc)

lookup : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → Vec A n → El n → A
lookup {n = 0}      _        ()
lookup {n = succ n} (x , xs) fzero     = x
lookup {n = succ n} (x , xs) (fsucc i) = lookup xs i

ElVec : ℕ → ℕ → Type₀
ElVec m n = Vec (El m) n

1C : {n : ℕ} → ElVec n n
1C {n} = tabulate id

infixr 80 _∘̂_
_∘̂_ : {n₀ n₁ n₂ : ℕ} → ElVec n₁ n₀ → ElVec n₂ n₁ → ElVec n₂ n₀
π₁ ∘̂ π₂ = tabulate (lookup π₂ ∘ lookup π₁)

record CPerm (values : ℕ) (size : ℕ) : Set where
  constructor cp
  field
    π  : ElVec values size
    πᵒ : ElVec size values
    αp : π ∘̂ πᵒ == 1C
    βp : πᵒ ∘̂ π == 1C

postulate
  perm-equiv : {m n : ℕ} → CPerm m n ≃ (El m ≃ El n)

perm-to-equiv : {m n : ℕ} → CPerm m n → El m ≃ El n
perm-to-equiv = p₁ perm-equiv

equiv-to-perm : {m n : ℕ} → El m ≃ El n → CPerm m n
equiv-to-perm = p₁ (p₂ perm-equiv)

ε : {m n : ℕ} → equiv-to-perm {m} {n} ∘ perm-to-equiv ∼ id
ε = p₁ (p₂ (p₂ perm-equiv))

η : {m n : ℕ} → perm-to-equiv {m} {n} ∘ equiv-to-perm ∼ id
η = p₁ (p₂ (p₂ (p₂ perm-equiv)))
