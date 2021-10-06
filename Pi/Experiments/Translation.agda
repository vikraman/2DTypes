{-# OPTIONS --without-K --exact-split --rewriting --allow-unsolved-metas #-}

open import lib.Base
open import lib.NType
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.types.Nat as N renaming (_+_ to _++_)

open import Pi.Common.Misc as N renaming (_*_ to _**_)
open import Pi.Common.Extra

module Pi.Experiments.Translation where

open import Pi.Syntax.Pi^ as Pi^
open import Pi.Syntax.Pi^Helpers as Pi^
open import Pi.Syntax.Pi as Pi

private
  variable
    m n o p q r : ℕ

eval₀ : Pi.U → ℕ
eval₀ O = O
eval₀ I = S O
eval₀ (t₁ + t₂) = eval₀ t₁ N.+ eval₀ t₂
eval₀ (t₁ × t₂) = eval₀ t₁ N.* eval₀ t₂

eval₀-size : {t₁ t₂ : Pi.U} (c : t₁ ⟷₁ t₂) → eval₀ t₁ == eval₀ t₂
eval₀-size unite₊l = idp
eval₀-size uniti₊l = idp
eval₀-size unite⋆l = +-unit-r (eval₀ _)
eval₀-size uniti⋆l = ! (eval₀-size unite⋆l)
eval₀-size swap₊ = +-comm (eval₀ _) (eval₀ _)
eval₀-size swap⋆ = TODO-
eval₀-size assocl₊ = +-assoc _ _ _
eval₀-size assocr₊ = ! (+-assoc _ _ _)
eval₀-size assocl⋆ = TODO-
eval₀-size assocr⋆ = TODO-
eval₀-size absorbr = idp
eval₀-size absorbl = TODO-
eval₀-size factorzr = ! (eval₀-size absorbl)
eval₀-size factorzl = idp
eval₀-size dist = TODO-
eval₀-size distl = TODO-
eval₀-size factor = TODO-
eval₀-size factorl = TODO-
eval₀-size id⟷₁ = idp
eval₀-size (c ◎ c₁) = ap eval₀ TODO-
eval₀-size (c ⊕ c₁) = TODO-
eval₀-size (c ⊗ c₁) = TODO-

private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

**^-l : {n m o : ℕ} → (n ⟷₁^ m) → (o ** n) ⟷₁^ (o ** m)
**^-l {o = O} c = id⟷₁^
**^-l {o = S o} c = ++^-⊕ c (**^-l {o = o} c)

**^-r : {n m o : ℕ} → (n ⟷₁^ m) → (n ** o) ⟷₁^ (m ** o)
**^-r {n} {m} {o} (swap₊^ {n = p}) =
  !⟷₁^ (++^-assoc o o (p ** o)) ◎^ ++^-r (++^-swap o o) ◎^ ++^-assoc o o (p ** o)
**^-r id⟷₁^ = id⟷₁^
**^-r (c₁ ◎^ c₂) = **^-r c₁ ◎^ **^-r c₂
**^-r (⊕^ c) = ++^-l (**^-r c)

**^-unit-l : (n : ℕ) → 1 ** n ⟷₁^ n
**^-unit-l O = id⟷₁^
**^-unit-l (S n) = ⊕^ **^-unit-l n

**^-unit-r : (n : ℕ) → n ** 1 ⟷₁^ n
**^-unit-r O = id⟷₁^
**^-unit-r (S n) = ⊕^ **^-unit-r n

dist^-r : (n m o : ℕ) → (n ++ m) ** o ⟷₁^ (n ** o) ++ (m ** o)
dist^-r O m o = id⟷₁^
dist^-r (S n) m o =
  ++^-l (dist^-r n m o) ◎^
  !⟷₁^ (++^-assoc o (n ** o) (m ** o))

dist^-l : (n m o : ℕ) → n ** (m ++ o) ⟷₁^ (n ** m) ++ (n ** o)
dist^-l O m o = id⟷₁^
dist^-l (S n) m o =
  ++^-l {o = m ++ o} (dist^-l n m o) ◎^
  ++^-assoc m o (n ** m ++ (n ** o)) ◎^
  ++^-l {o = m} (!⟷₁^ (++^-assoc o (n ** m) (n ** o))) ◎^
  ++^-l {o = m} (++^-r {o = n ** o} (++^-swap o (n ** m))) ◎^
  ++^-l {o = m} (++^-assoc (n ** m) o (n ** o)) ◎^
  !⟷₁^ (++^-assoc m (n ** m) (o ++ (n ** o)))

**^-assoc : (n m o : ℕ) → (n ** m) ** o ⟷₁^ n ** (m ** o)
**^-assoc O m o = id⟷₁^
**^-assoc (S n) m o = dist^-r m (n ** m) o ◎^ ++^-l (**^-assoc n m o)

**^-absorb-l : (n : ℕ) → 0 ** n ⟷₁^ 0
**^-absorb-l n = id⟷₁^

**^-absorb-r : (n : ℕ) → n ** 0 ⟷₁^ 0
**^-absorb-r O = id⟷₁^
**^-absorb-r (S n) = **^-absorb-r n

**^-cons : (n m : ℕ) → m ** (n ++ 1) ⟷₁^ (m ** n) ++ m
**^-cons n m = dist^-l m n 1 ◎^ ++^-l {o = m ** n} (**^-unit-r m)

**^-swap : (n m : ℕ) → (n ** m) ⟷₁^ (m ** n)
**^-swap O m = !⟷₁^ (**^-absorb-r m)
**^-swap (S n) m =
  ++^-l {o = m} (**^-swap n m) ◎^
  ++^-swap m (m ** n) ◎^
  !⟷₁^ (**^-cons n m) ◎^
  **^-l {o = m} (!⟷₁^ (++^-cons n))

**^-bigswap : {n m : ℕ} → (n ⟷₁^ m) → (2 ** n) ⟷₁^ (2 ** m)
**^-bigswap swap₊^ = swap₊^ ◎^ ⊕^ ⊕^ ++^-l swap₊^
**^-bigswap id⟷₁^ = id⟷₁^
**^-bigswap (c₁ ◎^ c₂) = **^-bigswap c₁ ◎^ **^-bigswap c₂
**^-bigswap (⊕^ c) = ⊕^ (++^-⊕ c (⊕^ (++^-r c)))

++^-hugeswap : {n m : ℕ} → (n ⟷₁^ m) → (n ++ n) ⟷₁^ (m ++ m)
++^-hugeswap swap₊^ = swap₊^ ◎^ ⊕^ ⊕^ ++^-l swap₊^
++^-hugeswap id⟷₁^ = id⟷₁^
++^-hugeswap (c₁ ◎^ c₂) = ++^-hugeswap c₁ ◎^ ++^-hugeswap c₂
++^-hugeswap (⊕^ c) = ⊕^ (++^-⊕ c (⊕^ c))

**^-⊗ : {n m o p : ℕ} → (n ⟷₁^ m) → (o ⟷₁^ p) → (n ** o) ⟷₁^ (m ** p)
**^-⊗ {n} {m} {o} {p} (swap₊^ {n = q}) c₂ =
  let r = **^-⊗ (id⟷₁^ {n}) c₂
  in !⟷₁^ (++^-assoc o o (q ** o)) ◎^
    ++^-⊕ (++^-hugeswap c₂) (**^-l {o = q} c₂) ◎^
    ++^-assoc p p (q ** p)
**^-⊗ (id⟷₁^ {n}) c₂ = **^-l {o = n} c₂
**^-⊗ (c₁ ◎^ c₃) c₂ = **^-⊗ c₁ c₂ ◎^ **^-⊗ c₃ id⟷₁^
**^-⊗ (⊕^ c₁) c₂ = ++^-⊕ c₂ (**^-⊗ c₁ c₂)

eval₁ : t₁ ⟷₁ t₂ → eval₀ t₁ ⟷₁^ eval₀ t₂
eval₁ unite₊l = id⟷₁^
eval₁ uniti₊l = id⟷₁^
eval₁ (unite⋆l {t = t}) = ++^-unit-r (eval₀ t)
eval₁ (uniti⋆l {t = t}) = !⟷₁^ (++^-unit-r (eval₀ t))
eval₁ (swap₊ {t₁ = t₁} {t₂ = t₂}) = ++^-swap (eval₀ t₁) (eval₀ t₂)
eval₁ (swap⋆ {t₁ = t₁} {t₂ = t₂}) = **^-swap (eval₀ t₁) (eval₀ t₂)
eval₁ (assocl₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}) = !⟷₁^ (++^-assoc (eval₀ t₁) (eval₀ t₂) (eval₀ t₃))
eval₁ (assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}) = ++^-assoc (eval₀ t₁) (eval₀ t₂) (eval₀ t₃)
eval₁ (assocl⋆ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}) = !⟷₁^ (**^-assoc (eval₀ t₁) (eval₀ t₂) (eval₀ t₃))
eval₁ (assocr⋆ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}) = **^-assoc (eval₀ t₁) (eval₀ t₂) (eval₀ t₃)
eval₁ (absorbr {t = t}) = **^-absorb-l (eval₀ t)
eval₁ (absorbl {t = t}) = **^-absorb-r (eval₀ t)
eval₁ (factorzr {t = t}) = !⟷₁^ (**^-absorb-r (eval₀ t))
eval₁ (factorzl {t = t}) = !⟷₁^ (**^-absorb-l (eval₀ t))
eval₁ (dist {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}) = dist^-r (eval₀ t₁) (eval₀ t₂) (eval₀ t₃)
eval₁ distl = TODO-
eval₁ (factor {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}) = !⟷₁^ (dist^-r (eval₀ t₁) (eval₀ t₂) (eval₀ t₃))
eval₁ (factorl {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}) = TODO-
eval₁ id⟷₁ = id⟷₁^
eval₁ (c₁ ◎ c₂) = eval₁ c₁ ◎^ eval₁ c₂
eval₁ (c₁ ⊕ c₂) = ++^-⊕ (eval₁ c₁) (eval₁ c₂)
eval₁ (c₁ ⊗ c₂) = **^-⊗ (eval₁ c₁) (eval₁ c₂)


