{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.Equiv.Equiv2HatHelpers where

open import Pi.Syntax.Pi+.Indexed as Pi
open import Pi.Syntax.Pi^ as Pi^
open import Pi.Syntax.Pi^Helpers as Pi^

open import lib.types.Nat renaming (_+_ to _++_)

open import Pi.Equiv.Equiv0Hat
open import Pi.Equiv.Equiv1Hat

open import HoTT hiding (_++_)

open import Pi.Common.Extra

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

++^-⊕-l-r : (c₁ : n₁ ⟷₁^ m₁) → (c₂ : n₂ ⟷₁^ m₂) → ++^-⊕ c₁ c₂ ⟷₂^ (++^-l c₂ ◎^ ++^-r c₁)
++^-⊕-l-r swap₊^ c₂ = swapl₊⟷₂^ ■^ (resp⊕⟷₂ (resp⊕⟷₂ (++^-⊕-id-l c₂)) ⊡^ id⟷₂^)
++^-⊕-l-r {O} id⟷₁^ c₂ = idr◎r^
++^-⊕-l-r {S n₁} id⟷₁^ c₂ = 
  let r = ++^-⊕-l-r {n₁} id⟷₁^ c₂
  in  resp⊕⟷₂ r ■^ resp⊕⟷₂ idr◎l^ ■^ idr◎r^
++^-⊕-l-r (c₁ ◎^ c₃) c₂ = 
  let r = ++^-⊕-l-r c₁ c₂ 
  in  (r ⊡^ ++^-⊕-id-r c₃) ■^ assoc◎r^
++^-⊕-l-r (⊕^ c₁) c₂ = resp⊕⟷₂ (++^-⊕-l-r c₁ c₂) ■^ hom⊕◎⟷₂^

private
  lemma : {n n₂ n₃ m₂ m₃ : ℕ} {c₂ : n₂ ⟷₁^ m₂} {c₃ : n₃ ⟷₁^ m₃} → 
      (++^-assoc n n₂ n₃ ◎^ ++^-l {o = n} (++^-⊕ c₂ c₃)) ⟷₂^ (++^-l c₃ ◎^ ++^-r {o = m₃} (++^-⊕ id⟷₁^ c₂) ◎^ ++^-assoc n m₂ m₃)
  lemma {O} {n₂} {n₃} {m₂} {m₃} {c₁} {c₂} = idl◎l^ ■^ ++^-⊕-l-r c₁ c₂ ■^ (id⟷₂^ ⊡^ idr◎r^)
  lemma {S n} {n₂} {n₃} {m₂} {m₃} {c₁} {c₂} = hom◎⊕⟷₂^ ■^ resp⊕⟷₂ (lemma {n} {n₂} {n₃} {m₂} {m₃} {c₁} {c₂}) ■^ hom⊕◎⟷₂^ ■^ (id⟷₂^ ⊡^ hom⊕◎⟷₂^)

++^-assoc-⊕ : {n₁ n₂ n₃ m₁ m₂ m₃ : ℕ} {c₁ : n₁ ⟷₁^ m₁} {c₂ : n₂ ⟷₁^ m₂} {c₃ : n₃ ⟷₁^ m₃} →
        (++^-assoc n₁ n₂ n₃) ◎^ (++^-⊕ c₁ (++^-⊕ c₂ c₃)) ⟷₂^
        (++^-⊕ (++^-⊕ c₁ c₂) c₃) ◎^ (++^-assoc m₁ m₂ m₃)
++^-assoc-⊕ {n₁ = n₁} {n₂ = n₂} {n₃ = n₃} {m₁ = m₁} {m₂ = m₂} {m₃ = m₃} {c₁ = (swap₊^ {n})} {c₂ = c₂} {c₃ = c₃} = 
  (_ ◎^ swap₊^ ◎^ _)  ⟷₂^⟨ assoc◎l^ ⟩
  (_ ◎^ swap₊^) ◎^ _ ⟷₂^⟨ swapr₊⟷₂^ ⊡^ resp⊕⟷₂ (resp⊕⟷₂ ((++^-⊕-id-l {n₂ ++ n₃} {m₂ ++ m₃} {n} (++^-⊕ c₂ c₃)))) ⟩
  (swap₊^ ◎^ _) ◎^ _ ⟷₂^⟨ assoc◎r^ ⟩
  (swap₊^ ◎^ _) ⟷₂^⟨ id⟷₂^ ⊡^ hom◎⊕⟷₂^ ⟩
  (swap₊^ ◎^ _) ⟷₂^⟨ id⟷₂^ ⊡^ resp⊕⟷₂ hom◎⊕⟷₂^ ⟩
  (swap₊^ ◎^ _) ⟷₂^⟨ id⟷₂^ ⊡^ resp⊕⟷₂ (resp⊕⟷₂ lemma) ⟩
  (swap₊^ ◎^ _) ⟷₂^⟨ id⟷₂^ ⊡^ (resp⊕⟷₂ hom⊕◎⟷₂^) ⟩
  (swap₊^ ◎^ _) ⟷₂^⟨ id⟷₂^ ⊡^ hom⊕◎⟷₂^ ⟩
  (swap₊^ ◎^ _) ⟷₂^⟨ id⟷₂^ ⊡^ ((id⟷₂^ ⊡^ resp⊕⟷₂ hom⊕◎⟷₂^)) ⟩
  (swap₊^ ◎^ _) ⟷₂^⟨ id⟷₂^ ⊡^ (id⟷₂^ ⊡^ hom⊕◎⟷₂^ )⟩
  (swap₊^ ◎^ _) ⟷₂^⟨ id⟷₂^ ⊡^ (resp⊕⟷₂ (resp⊕⟷₂ (!⟷₂^ (++^-⊕-id-l c₃))) ⊡^ (resp⊕⟷₂ (resp⊕⟷₂ (!⟷₂^ (++^-⊕-id-r (++^-⊕ id⟷₁^ c₂)))) ⊡^ id⟷₂^)) ⟩
  _ ⟷₂^⟨ assoc◎l^ ⟩
  _ ⟷₂^⟨ assoc◎l^ ⟩
  _ ⟷₂^∎
++^-assoc-⊕ {O} {c₁ = id⟷₁^} = idl◎l^ ■^ idr◎r^
++^-assoc-⊕ {S n₁} {c₁ = id⟷₁^} {c₂} {c₃} = 
    let r = ++^-assoc-⊕ {n₁} {c₁ = id⟷₁^} {c₂} {c₃}
    in  (hom◎⊕⟷₂^ ■^ resp⊕⟷₂ r) ■^ hom⊕◎⟷₂^
++^-assoc-⊕ {c₁ = c ◎^ d} {c₂} {c₃} = TODO! -- Use ++^-⊕-id-r to reduce ++^-⊕ to ++^-r and use recursive call
++^-assoc-⊕ {c₁ = ⊕^ c₁} = hom◎⊕⟷₂^ ■^ resp⊕⟷₂ (++^-assoc-⊕ {c₁ = c₁}) ■^ (!⟷₂^ hom◎⊕⟷₂^)
