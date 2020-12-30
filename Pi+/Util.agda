{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Util where

open import lib.Base
open import lib.types.Nat renaming (_+_ to _+ℕ_)
open import lib.types.Fin
open import lib.types.Sigma
open import lib.PathGroupoid

open import Pi+.Syntax as Pi
open import Pi+.Level0

split : ∀ {n m} → ⟪ n +ℕ m ⟫ ⟷₁ ⟪ n ⟫ + ⟪ m ⟫
split {O} {m} = uniti₊l
split {S n} {m} = (id⟷₁ ⊕ split) ◎ assocl₊

-- swap i and i-1
swap[_] : ∀ {n} → Fin (1 +ℕ n) → ⟪ 2 +ℕ n ⟫ ⟷₁ ⟪ 2 +ℕ n ⟫
swap[_] {n} (i , i<1+n) = transport (λ m → ⟪ m ⟫ ⟷₁ ⟪ m ⟫) (snd diff) c
  where
  diff : Σ ℕ (λ k → (S (S i)) +ℕ k == 2 +ℕ n)
  diff with <-witness i<1+n
  ... | (k , p) = k , ap S (ap S (+-comm i k) ∙ p)

  swap : ∀ {m} → ⟪ 2 +ℕ m ⟫ ⟷₁ ⟪ 2 +ℕ m ⟫
  swap {O} = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
  swap {S m} = id⟷₁ ⊕ swap

  c : ⟪ S (S i) +ℕ fst diff ⟫ ⟷₁ ⟪ S (S i) +ℕ fst diff ⟫
  c = split {S (S i)} {fst diff} ◎ (swap ⊕ id⟷₁) ◎ !⟷₁ split

swap[_,_⟦_⟧] : ∀ {n} → (i j : Fin (2 +ℕ n)) → (fst i < fst j) → ⟪ 2 +ℕ n ⟫ ⟷₁ ⟪ 2 +ℕ n ⟫
swap[_,_⟦_⟧] {n} (i , i<2+n) (S i , j<2+n) ltS = swap[ (i , <-cancel-S j<2+n) ]
swap[_,_⟦_⟧] {n} (i , i<2+n) (S j , j<2+n) (ltSR i<j) = swap[ (j , <-cancel-S j<2+n) ]
                                                      ◎ swap[ (i , i<2+n) , (j , <-trans (<-cancel-S j<2+n) ltS) ⟦ i<j ⟧]
