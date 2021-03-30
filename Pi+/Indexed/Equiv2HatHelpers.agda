{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.Indexed.Equiv2HatHelpers where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.Indexed.SyntaxHatHelpers as Pi^

open import lib.types.Nat renaming (_+_ to _++_)

open import Pi+.Indexed.Equiv0Hat
open import Pi+.Indexed.Equiv1Hat

open import HoTT hiding (_++_)

open import Pi+.Extra

private
    variable
        n n₁ n₂ n₃ m₁ m₂ m₃ m o : ℕ
        t₁ t₂ t₃ : U n
        c₁ c₂ c₃ : n ⟷₁^ m

!-triangle^ : {c₁ : n ⟷₁^ m} {c₂ : m ⟷₁^ n} → (c₁ ◎^ c₂) ⟷₂^ id⟷₁^ → c₁ ⟷₂^ (!⟷₁^ c₂)
!-triangle^ {c₁ = c₁} {c₂ = c₂} α =
  c₁ ⟷₂^⟨ idr◎r^ ⟩
  c₁ ◎^ id⟷₁^ ⟷₂^⟨ id⟷₂^ ⊡^ linv◎r^ ⟩
  c₁ ◎^ (c₂ ◎^ !⟷₁^ c₂) ⟷₂^⟨ assoc◎l^ ⟩
  (c₁ ◎^ c₂) ◎^ !⟷₁^ c₂ ⟷₂^⟨ α ⊡^ id⟷₂^ ⟩
  id⟷₁^  ◎^ !⟷₁^ c₂ ⟷₂^⟨ idl◎l^ ⟩
  !⟷₁^ c₂ ⟷₂^∎

eval^₁-! : (c : t₁ ⟷₁ t₂) → eval^₁ (!⟷₁ c) ⟷₂^ !⟷₁^ (eval^₁ c)
eval^₁-! unite₊l = id⟷₂^
eval^₁-! uniti₊l = id⟷₂^
eval^₁-! (swap₊ {t₁ = t₁} {t₂ = t₂}) = !-triangle^ (++^-symm (eval^₀ t₂) (eval^₀ t₁))
eval^₁-! (assocl₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}) = !⟷₂^ (!!⟷₁^ (++^-assoc (eval^₀ t₁) (eval^₀ t₂) (eval^₀ t₃)))
eval^₁-! assocr₊ = id⟷₂^
eval^₁-! id⟷₁ = id⟷₂^
eval^₁-! (c₁ ◎ c₂) = eval^₁-! c₂ ⊡^ eval^₁-! c₁
eval^₁-! (c₁ ⊕ c₂) = ++^-⊕-◎ (eval^₁-! c₁) (eval^₁-! c₂) ■^ ++^-⊕-! (eval^₁ c₁) (eval^₁ c₂)

eval^₁-◎ : (c₁ : t₁ ⟷₁ t₂) (c₂ : t₂ ⟷₁ t₃) → eval^₁ (c₁ ◎ c₂) ⟷₂^ (eval^₁ c₁) ◎^ (eval^₁ c₂)
eval^₁-◎ unite₊l c₂ = id⟷₂^
eval^₁-◎ uniti₊l c₂ = id⟷₂^
eval^₁-◎ swap₊ c₂ = id⟷₂^
eval^₁-◎ assocl₊ c₂ = id⟷₂^
eval^₁-◎ assocr₊ c₂ = id⟷₂^
eval^₁-◎ id⟷₁ c₂ = id⟷₂^
eval^₁-◎ (c₁ ◎ c₃) c₂ = id⟷₂^
eval^₁-◎ (c₁ ⊕ c₃) c₂ = id⟷₂^

+-assoc' : (k m n : ℕ) → (k ++ m) ++ n == k ++ (m ++ n)
+-assoc' 0     m n = idp
+-assoc' (S k) m n = ap S (+-assoc' k m n)


-- ++^-assoc-id : (++^-id (+-assoc' n m o)) ⟷₂^ ++^-assoc n m o
-- ++^-assoc-id {O} {m} {o} = id⟷₂^
-- ++^-assoc-id {S n} {m} {o} =
--   let r = ++^-assoc-id {n} {m} {o}
--   in  {!   !} ■^ {!   !}

-- postulate
--         -- Temporary
--         -- theorem : ++^-⊕-id-l
--     plus-rewrite : {n m o : ℕ} {c : n ⟷₁^ m} → ++^-⊕ (id⟷₁^ {o}) c ↦ ++^-l c -- because proof of == in ℕ
--     {-# REWRITE plus-rewrite #-}

++^-assoc-⊕ : ∀ {c₁ : n₁ ⟷₁^ m₁} {c₂ : n₂ ⟷₁^ m₂} {c₃ : n₃ ⟷₁^ m₃} →
        (++^-assoc n₁ n₂ n₃) ◎^ (++^-⊕ c₁ (++^-⊕ c₂ c₃)) ⟷₂^
        (++^-⊕ (++^-⊕ c₁ c₂) c₃) ◎^ (++^-assoc m₁ m₂ m₃)
++^-assoc-⊕ {c₁ = (swap₊^ {n})} {c₂ = c₂} {c₃ = c₃} = TODO!
++^-assoc-⊕ {c₁ = id⟷₁^} = TODO!
++^-assoc-⊕ {c₁ = c₁ ◎^ c₂} = TODO!
++^-assoc-⊕ {c₁ = ⊕^ c₁} = hom◎⊕⟷₂^ ■^ resp⊕⟷₂ (++^-assoc-⊕ {c₁ = c₁}) ■^ (!⟷₂^ hom◎⊕⟷₂^)
