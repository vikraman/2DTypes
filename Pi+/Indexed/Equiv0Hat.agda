{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.Indexed.Equiv0Hat where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.UFin
open import Pi+.Extra

open import lib.Basics
open import lib.types.Fin
open import lib.types.List hiding (_++_)
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct
open import lib.types.Nat as N renaming (_+_ to _++_)

private
  variable
    n m o p : ℕ

++^-id : {n m : ℕ} → (n == m) → n ⟷₁^ m
++^-id p = transport (λ n → _ ⟷₁^ n) p id⟷₁^

-- ++^-id {O} {O} p = id⟷₁^
-- ++^-id {S n} {S m} p = ⊕^ (++^-id (ℕ-S-is-inj n m p))

++^-cons : (n : ℕ) → (S n) ⟷₁^ (n ++ 1)
++^-cons O = id⟷₁^
++^-cons (S n) = swap₊^ ◎^ (⊕^ (++^-cons n))

++^-⊕ : {n m o p : ℕ} → (n ⟷₁^ m) → (o ⟷₁^ p) → (n ++ o) ⟷₁^ (m ++ p)
++^-⊕ (swap₊^ {n = n}) c₂ = big-swap₊^ (++^-⊕ id⟷₁^ c₂)
++^-⊕ {O} id⟷₁^ c₂ = c₂
++^-⊕ {S n} id⟷₁^ c₂ = ⊕^ (++^-⊕ {n} id⟷₁^ c₂)
++^-⊕ (c₁ ◎^ c₃) c₂ = (++^-⊕ c₁ c₂) ◎^ ++^-⊕ c₃ id⟷₁^
++^-⊕ (⊕^ c₁) c₂ = ⊕^ (++^-⊕ c₁ c₂)

++^-swap : (n m : ℕ) → (n ++ m) ⟷₁^ (m ++ n)
++^-swap O m = ++^-id (! (+-unit-r m))
++^-swap (S n) m = (⊕^ ++^-swap n m) ◎^ ++^-cons (m ++ n) ◎^ !⟷₁^ (++^-id (! (+-assoc m n (S O)))) ◎^ ++^-⊕ id⟷₁^ (!⟷₁^ (++^-cons n))

quote^₀ : (n : ℕ) → U n
quote^₀ O = O
quote^₀ (S n) = I U.+ quote^₀ n

quote^₀++ : (n m : ℕ) → quote^₀ (n ++ m) ⟷₁ quote^₀ n U.+ quote^₀ m
quote^₀++ O m = uniti₊l
quote^₀++ (S n) m = (id⟷₁ ⊕ quote^₀++ n m) ◎ assocl₊

eval^₀ : U n → ℕ
eval^₀ {n} t = n

quote-eval^₀ : (t : U n) → quote^₀ (eval^₀ t) ⟷₁ t
quote-eval^₀ O = id⟷₁
quote-eval^₀ I = unite₊r
quote-eval^₀ (t₁ U.+ t₂) = quote^₀++ (eval^₀ t₁) (eval^₀ t₂) ◎ (quote-eval^₀ t₁ ⊕ quote-eval^₀ t₂)

eval-quote^==₀ : (n : ℕ) → eval^₀ (quote^₀ n) == n
eval-quote^==₀ n = idp

eval-quote^₀ : (n : ℕ) → eval^₀ (quote^₀ n) ⟷₁^ n
eval-quote^₀ n = id⟷₁^
