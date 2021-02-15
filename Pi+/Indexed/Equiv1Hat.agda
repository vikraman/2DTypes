{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Indexed.Equiv1Hat where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.UFin
open import Pi+.Extra

open import Pi+.Indexed.Equiv0Hat

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.BAut
open import lib.types.Nat
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct
open import lib.types.Sigma


private
    variable
        n m : ℕ    

quote^₁ : {t₁ : U^ n} {t₂ : U^ m} → (t₁ ⟷₁^ t₂) → (quote^₀ t₁ ⟷₁ quote^₀ t₂)
quote^₁ swap₊^ = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
quote^₁ id⟷₁^ = id⟷₁
quote^₁ (t ◎^ t₁) = quote^₁ t ◎ quote^₁ t₁
quote^₁ (⊕^ t) = id⟷₁ ⊕ quote^₁ t

denorm : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → quote^₀ (eval^₀ t₁) ⟷₁ quote^₀ (eval^₀ t₂)
denorm {t₁ = t₁} {t₂ = t₂} c = (quote-eval^₀ t₁ ◎ c ◎ !⟷₁ (quote-eval^₀ t₂))

denorm← : {t₁ : U n} {t₂ : U m} → (c : quote^₀ (eval^₀ t₁) ⟷₁ quote^₀ (eval^₀ t₂)) → t₁ ⟷₁ t₂
denorm← {t₁ = t₁} {t₂ = t₂} c = (!⟷₁ (quote-eval^₀ t₁)) ◎ c ◎ (quote-eval^₀ t₂)

norm : {t₁ : U^ n} {t₂ : U^ m} → (c : t₁ ⟷₁^ t₂) → eval^₀ (quote^₀ t₁) ⟷₁^ eval^₀ (quote^₀ t₂)
norm {t₁ = t₁} {t₂ = t₂} c = (eval-quote^₀ t₁ ◎^ c ◎^ !⟷₁^ (eval-quote^₀ t₂)) -- 

eval^₁ : {t₁ : U n} {t₂ : U m} → (t₁ ⟷₁ t₂) → (eval^₀ t₁ ⟷₁^ eval^₀ t₂)
eval^₁ unite₊l = id⟷₁^
eval^₁ uniti₊l = id⟷₁^
eval^₁ (swap₊ {t₁ = t₁} {t₂ = t₂}) = ++^-swap (eval^₀ t₁) (eval^₀ t₂)
eval^₁ (assocl₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}) = ++^-assoc (eval^₀ t₁) (eval^₀ t₂) (eval^₀ t₃)
eval^₁ (assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}) = !⟷₁^ (++^-assoc (eval^₀ t₁) (eval^₀ t₂) (eval^₀ t₃))
eval^₁ id⟷₁ = id⟷₁^
eval^₁ (c₁ ◎ c₂) = eval^₁ c₁ ◎^ eval^₁ c₂
eval^₁ (c₁ ⊕ c₂) = ++^-⊕ (eval^₁ c₁) (eval^₁ c₂)

eval-quote^₁ : {t₁ : U^ n} {t₂ : U^ m} → (c : t₁ ⟷₁^ t₂) → eval^₁ (quote^₁ c) ⟷₂^ norm c
eval-quote^₁ (swap₊^ {t = t}) = {!   !}
    -- let cc = eval-quote^₀ t
    -- in  !⟷₂^ ( -- ) -- (swapl₊⟷₂^ {c = {! id⟷₁^  !}})
    --     (⊕^ ⊕^ cc) ◎^ (swap₊^ ◎^ ⊕^ (⊕^ (!⟷₁^ cc))) ⟷₂^⟨ _⊡^_ {c₁ = (⊕^ ⊕^ cc)} {c₂ = _} {c₃ = (⊕^ ⊕^ cc)} {c₄ = ((⊕^ (⊕^ !⟷₁^ cc)) ◎^ swap₊^)} {!   !}  {! swapl₊⟷₂^ !} ⟩
    --     {!   !} ⟷₂^⟨ {!   !} ⟩ -- (⊕^ ⊕^ cc) ◎^ ((⊕^ (⊕^ !⟷₁^ cc)) ◎^ swap₊^) ,, assoc◎l^
    --     ((⊕^ ⊕^ cc) ◎^ (⊕^ (⊕^ !⟷₁^ (cc)))) ◎^ swap₊^ ⟷₂^⟨ hom◎⊕⟷₂^ ⊡^ id⟷₂^ ⟩
    --     (⊕^ ((⊕^ cc) ◎^ (⊕^ !⟷₁^ (cc)))) ◎^ swap₊^ ⟷₂^⟨ (resp⊕⟷₂ hom◎⊕⟷₂^) ⊡^ id⟷₂^ ⟩
    --     (⊕^ (⊕^ ((cc) ◎^ (!⟷₁^ (cc))))) ◎^ swap₊^ ⟷₂^⟨ (resp⊕⟷₂ (resp⊕⟷₂ linv◎l^)) ⊡^ id⟷₂^ ⟩
    --     (⊕^ (⊕^ (id⟷₁^))) ◎^ swap₊^ ⟷₂^⟨ id⟷₂^ ⟩
    --     swap₊^ ⟷₂^∎)
eval-quote^₁ {n = n} {t₁ = t₁} id⟷₁^ = {!   !} -- !⟷₂^ (linv◎l^ {n} {t₁ = eval^₀ (quote^₀ t₁)} {t₂ = t₁} {c = eval-quote^₀ _})
eval-quote^₁ (c ◎^ c₁) = {!   !}
eval-quote^₁ (⊕^ c) = {!   !}

quote-eval^₁ : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → quote^₁ (eval^₁ c) ⟷₂ denorm c
quote-eval^₁ unite₊l = {!   !}
quote-eval^₁ uniti₊l = {!   !}
quote-eval^₁ swap₊ = {!   !}
quote-eval^₁ assocl₊ = {!   !}
quote-eval^₁ assocr₊ = {!   !}
quote-eval^₁ id⟷₁ = {!   !}
quote-eval^₁ (c ◎ c₁) = {!   !}
quote-eval^₁ (c ⊕ c₁) = {!   !}