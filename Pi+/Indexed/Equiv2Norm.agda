{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

module Pi+.Indexed.Equiv2Norm where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.UFin
open import Pi+.Extra
open import Pi+.UFin.BAut

open import Pi+.Indexed.Equiv0Norm
open import Pi+.Indexed.Equiv1Norm

open import HoTT
-- open import lib.Basics
-- open import lib.types.Fin
-- open import lib.types.List
-- open import lib.types.Truncation
-- open import lib.Equivalence
-- open import lib.NType2
-- open import lib.types.SetQuotient
-- open import lib.types.Coproduct

private
    variable
        n m : ℕ

e= : ∀ {i} {X : Type i} {e₁ e₂ : Fin n ≃ X} → ((f : Fin n) → (–> e₁ f == –> e₂ f)) → e₁ == e₂
e= h = pair= (λ= h) prop-has-all-paths-↓

evalNorm₂ : {c₁ c₂ : n ⟷₁^ m} → c₁ ⟷₂^ c₂ → evalNorm₁ c₁ == evalNorm₁ c₂
evalNorm₂ {O} {m} {(c₁ ◎^ c₂ ◎^ c₃)} assoc◎l^ with (⟷₁^-eq-size (c₁ ◎^ c₂ ◎^ c₃))
evalNorm₂ {O} {O} {c₁ ◎^ c₂ ◎^ c₃} assoc◎l^ | idp with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂) | (⟷₁^-eq-size c₃)
... | idp | idp | idp = idp
evalNorm₂ {O} {m} {.((_ ◎^ _) ◎^ _)} (assoc◎r^ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}) with (⟷₁^-eq-size ((c₁ ◎^ c₂) ◎^ c₃))
evalNorm₂ {O} {O} {(_ ◎^ _) ◎^ _} (assoc◎r^ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}) | idp with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂) | (⟷₁^-eq-size c₃)
... | idp | idp | idp = idp
evalNorm₂ {O} {m} {.(id⟷₁^ ◎^ _)} idl◎l^ = TODO
evalNorm₂ {O} {m} {c₁} idl◎r^ = TODO
evalNorm₂ {O} {m} {.(_ ◎^ id⟷₁^)} idr◎l^ = TODO
evalNorm₂ {O} {m} {c₁} idr◎r^ = TODO
evalNorm₂ {O} {.0} {.(_ ◎^ !⟷₁^ _)} linv◎l^ = TODO
evalNorm₂ {O} {.0} {.id⟷₁^} linv◎r^ = TODO
evalNorm₂ {O} {.0} {.(!⟷₁^ _ ◎^ _)} rinv◎l^ = TODO
evalNorm₂ {O} {.0} {.id⟷₁^} rinv◎r^ = TODO
evalNorm₂ {O} {m} {c₁} id⟷₂^ with (⟷₁^-eq-size c₁)
... | idp = idp
evalNorm₂ {O} {m} {c₁} {c₂} (trans⟷₂^ α α₁) with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂)
... | idp | idp = idp
evalNorm₂ {O} {m} {.(_ ◎^ _)} (α ⊡^ α₁) = TODO
evalNorm₂ {S n} {m} {.(_ ◎^ _ ◎^ _)} {.((_ ◎^ _) ◎^ _)} assoc◎l^ = TODO
evalNorm₂ {S n} {m} {.((_ ◎^ _) ◎^ _)} {.(_ ◎^ _ ◎^ _)} assoc◎r^ = TODO
evalNorm₂ {S n} {m} {.(id⟷₁^ ◎^ c₂)} {c₂} idl◎l^ = TODO
evalNorm₂ {S n} {m} {c₁} {.(id⟷₁^ ◎^ c₁)} idl◎r^ = TODO
evalNorm₂ {S n} {m} {.(c₂ ◎^ id⟷₁^)} {c₂} idr◎l^ = TODO
evalNorm₂ {S n} {m} {c₁} {.(c₁ ◎^ id⟷₁^)} idr◎r^ = TODO
evalNorm₂ {S n} {.(S n)} {.(_ ◎^ !⟷₁^ _)} {.id⟷₁^} linv◎l^ = TODO
evalNorm₂ {S n} {.(S n)} {.id⟷₁^} {.(_ ◎^ !⟷₁^ _)} linv◎r^ = TODO
evalNorm₂ {S n} {.(S n)} {.(!⟷₁^ _ ◎^ _)} {.id⟷₁^} rinv◎l^ = TODO
evalNorm₂ {S n} {.(S n)} {.id⟷₁^} {.(!⟷₁^ _ ◎^ _)} rinv◎r^ = TODO
evalNorm₂ {S n} {m} {c₁} {.c₁} id⟷₂^ with (⟷₁^-eq-size c₁)
... | idp = idp
evalNorm₂ {S n} {m} {c₁} {c₂} (trans⟷₂^ α α₁) = TODO
evalNorm₂ {S n} {m} {.(_ ◎^ _)} {.(_ ◎^ _)} (α ⊡^ α₁) = TODO
evalNorm₂ {S n} {.(S n)} {.(⊕^ id⟷₁^)} {.id⟷₁^} ⊕id⟷₁⟷₂^ = TODO
evalNorm₂ {S n} {.(S n)} {.id⟷₁^} {.(⊕^ id⟷₁^)} !⊕id⟷₁⟷₂^ = TODO
evalNorm₂ {S n} {.(S _)} {.((⊕^ _) ◎^ ⊕^ _)} {.(⊕^ _ ◎^ _)} hom◎⊕⟷₂^ = TODO
evalNorm₂ {S n} {.(S _)} {.(⊕^ _)} {.(⊕^ _)} (resp⊕⟷₂ α) = TODO
evalNorm₂ {S n} {.(S _)} {.(⊕^ _ ◎^ _)} {.((⊕^ _) ◎^ ⊕^ _)} hom⊕◎⟷₂^ = TODO
evalNorm₂ {S .(S _)} {.(S (S _))} {.((⊕^ ⊕^ _) ◎^ swap₊^)} {.(swap₊^ ◎^ ⊕^ ⊕^ _)} swapr₊⟷₂^ = TODO
evalNorm₂ {S .(S _)} {.(S (S _))} {.(swap₊^ ◎^ ⊕^ ⊕^ _)} {.((⊕^ ⊕^ _) ◎^ swap₊^)} swapl₊⟷₂^ =
  e= (λ { (O , p) → TODO ; (S n , p) → TODO })

-- evalNorm₂ id⟷₂^ = idp
-- evalNorm₂ (trans⟷₂^ α α₁) = evalNorm₂ α ∙ evalNorm₂ α₁

-- _ : evalNorm₁ (swap₊^ {n = 0} ◎^ swap₊^ {n = 0}) == evalNorm₁ id⟷₁^

_ : {n : ℕ} → evalNorm₁ (id⟷₁^ {n = n}) == evalNorm₁ (id⟷₁^ {n = n})
_ = e= (λ { (O , p) → idp ; (S n , p) → idp })

_ : evalNorm₁ (swap₊^ {n = n} ◎^ swap₊^ {n = n}) == evalNorm₁ id⟷₁^
_ = e= (λ { (O , p) → idp ; (S n , p) → idp })
