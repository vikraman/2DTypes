{-# OPTIONS --without-K #-}

module 2D.SingIter where

open import 2D.Types using (U; _⟷_; _◎_; _⇔_; _⊡_; _●_; 2!)

open import 2D.Sing
open import 2D.Iter
open import 2D.Power

----------------------------------------------------------------------------
-- Generally useful lemmas relating Sing and ITer

-- we can always exchange a Sing and an Iter
swapSI : {τ : U} {p : τ ⟷ τ} (r : Sing p) (p^i : Iter p) →
  Sing.p' r ◎ Iter.q p^i ⇔ Iter.q p^i ◎ Sing.p' r
swapSI ⟪ p' , eq ⟫ < k , q , α > = eq ⊡ α ● assoc1g k ● 2! α ⊡ 2! eq
