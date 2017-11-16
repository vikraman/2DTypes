module PiFin.Perm where

open import IntensionalTypeTheory

data Fin : ℕ → Set where
  z : ∀ {n} → Fin (succ n)
  s : ∀ {n} → Fin n → Fin (succ n)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

len : ∀ {A} → List A → ℕ
len [] = zero
len (x ∷ xs) = succ (len xs)

_++_ : ∀ {A} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-idr : ∀ {A : Set} (xs : List A) → (xs ++ []) == xs
++-idr [] = refl []
++-idr (x ∷ xs) = ap (_∷_ x) (++-idr xs)

rep : ∀ {A} → ℕ → A → List A
rep zero x = []
rep (succ n) x = x ∷ rep n x

data _∪_≡_ {A : Set} (m : A) : List A → List A → Set where
  here : ∀ {ms}
       → m ∪ ms ≡ (m ∷ ms)
  there : ∀ {n ns mns}
        → m ∪ ns ≡ mns
        → m ∪ (n ∷ ns) ≡ (n ∷ mns)

data IsPerm {A : Set} : List A → List A → Set where
  []  : IsPerm [] []
  _∷_ : ∀ {m ms ns mns}
      → m ∪ ns ≡ mns
      → IsPerm ms ns
      → IsPerm (m ∷ ms) mns

open import PiFin.Syntax

El : U → List 𝟙
El ZERO = []
El ONE = 0₁ ∷ []
El (PLUS T₁ T₂) = El T₁ ++ El T₂
El (TIMES T₁ T₂) = rep (mult (len (El T₁)) (len (El T₂))) 0₁

IsPerm-refl : ∀ {A : Set} (xs : List A) → IsPerm xs xs
IsPerm-refl [] = []
IsPerm-refl (x ∷ xs) = here ∷ IsPerm-refl xs

data R* {A : Set} (R : A → A → Set) : A → A → Set where
  r-id : ∀ {a b} → R a b → R* R a b
  r-sym : ∀ {a b} → R a b → R* R b a
  r-trans : ∀ {a b c} → R a b → R* R b c → R* R a c

Perm : {A : Set} → List A → List A → Set
Perm = R* IsPerm

Perm-++ : ∀ {A : Set} {xs ys : List A} → Perm (xs ++ ys) (ys ++ xs)
Perm-++ {A} {[]} {ys} = r-id (tpt (λ xs → IsPerm xs (ys ++ [])) (++-idr ys) (IsPerm-refl (ys ++ [])))
Perm-++ {A} {x ∷ xs} {ys} with Perm-++ {A} {xs} {ys}
... | p = {!!}

lemma : {X Y : U} → X ⟷ Y → Perm (El X) (El Y)
lemma {.(PLUS ZERO Y)} {Y} unite₊l = r-id (IsPerm-refl (El Y))
lemma {.(PLUS _ _)} {.(PLUS _ _)} swap₊ = {!!}
lemma {.(PLUS _ (PLUS _ _))} {.(PLUS (PLUS _ _) _)} assocl₊ = {!!}
lemma {.(TIMES ONE Y)} {Y} unite⋆l = {!!}
lemma {.(TIMES _ _)} {.(TIMES _ _)} swap⋆ = {!!}
lemma {.(TIMES _ (TIMES _ _))} {.(TIMES (TIMES _ _) _)} assocl⋆ = {!!}
lemma {.(TIMES ZERO _)} {.ZERO} absorbr = {!!}
lemma {.(TIMES (PLUS _ _) _)} {.(PLUS (TIMES _ _) (TIMES _ _))} dist = {!!}
lemma {X} {.X} id⟷ = {!!}
lemma {X} {Y} (_⟷_.! p) = {!!}
lemma {X} {Y} (p ◎ p₃) = {!!}
lemma {.(PLUS _ _)} {.(PLUS _ _)} (p ⊕ p₃) = {!!}
lemma {.(TIMES _ _)} {.(TIMES _ _)} (p ⊗ p₃) = {!!}
