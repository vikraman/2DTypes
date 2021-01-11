{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Util where

open import lib.Base
open import lib.types.Nat renaming (_+_ to _+ℕ_)
open import lib.types.Fin
open import lib.types.Sigma
open import lib.PathGroupoid

-- open import Pi+.Syntax as Pi
open import Pi+.Level0

-- swap i-th and j-th position
swap[_,_]⟦_,_⟧ : ∀ {n} → (i j : ℕ) → i < j → j < 2 +ℕ n → ⟪ 2 +ℕ n ⟫ ⟷₁ ⟪ 2 +ℕ n ⟫
swap[_,_]⟦_,_⟧ {n}   0 .1 ltS j<2+n = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
swap[_,_]⟦_,_⟧ {0}   0 (S (S j)) (ltSR i<j) j<2+n = ⊥-elim (≮O j (<-cancel-S (<-cancel-S j<2+n)))
swap[_,_]⟦_,_⟧ {S n} 0 (S j) (ltSR i<j) j<2+n = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊ ◎ (id⟷₁ ⊕ swap[ 0 , j ]⟦ i<j , <-cancel-S j<2+n ⟧)
swap[_,_]⟦_,_⟧ {0} (S i) (S .(S i)) ltS j<2+n = ⊥-elim (≮O i (<-cancel-S (<-cancel-S j<2+n)))
swap[_,_]⟦_,_⟧ {0} (S i) (S j) (ltSR i<j) j<2+n = ⊥-elim (≮O i (<-cancel-S (<-cancel-S (<-trans (<-ap-S i<j) j<2+n))))
swap[_,_]⟦_,_⟧ {S n} (S i) .(S (S i)) ltS j<2+n = id⟷₁ ⊕ swap[ i , (S i) ]⟦ ltS , <-cancel-S j<2+n ⟧
swap[_,_]⟦_,_⟧ {S n} (S i) (S j) (ltSR i<j) j<2+n = id⟷₁ ⊕ swap[ i , j ]⟦ <-trans ltS i<j , <-cancel-S j<2+n ⟧
