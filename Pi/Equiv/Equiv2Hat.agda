{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

module Pi.Equiv.Equiv2Hat where

open import Pi.Syntax.Pi+.Indexed as Pi
open import Pi.Syntax.Pi^ as Pi^
open import Pi.Syntax.Pi^Helpers as Pi^
open import Pi.Equiv.Equiv1NormHelpers
open import Pi.Equiv.Equiv2HatHelpers
open import Pi.UFin.UFin
open import Pi.Common.Extra
open import Pi.UFin.BAut

open import Pi.Equiv.Equiv0Hat
open import Pi.Equiv.Equiv1Hat

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct
open import lib.types.Nat as N

private
    variable
        n m : ℕ

!-quote^₁ : (c : n ⟷₁^ m) → quote^₁ (!⟷₁^ c) ⟷₂ !⟷₁ (quote^₁ c)
!-quote^₁ swap₊^ = assoc◎l
!-quote^₁ id⟷₁^ = id⟷₂
!-quote^₁ (c ◎^ c₁) = (!-quote^₁ c₁) ⊡ (!-quote^₁ c)
!-quote^₁ (⊕^ c) = resp⊕⟷₂ id⟷₂ (!-quote^₁ c)

quote^₂ : {c₁ c₂ : n ⟷₁^ m} → c₁ ⟷₂^ c₂ → quote^₁ c₁ ⟷₂ quote^₁ c₂
quote^₂ assoc◎l^ = assoc◎l
quote^₂ assoc◎r^ = assoc◎r
quote^₂ idl◎l^ = idl◎l
quote^₂ idl◎r^ = idl◎r
quote^₂ idr◎l^ = idr◎l
quote^₂ idr◎r^ = idr◎r
quote^₂ linv◎l^ = _■_ (id⟷₂ ⊡ (!-quote^₁ _)) linv◎l
quote^₂ linv◎r^ = !⟷₂ (_■_ (id⟷₂ ⊡ (!-quote^₁ _)) linv◎l)
quote^₂ rinv◎l^ = _■_ ( (!-quote^₁ _) ⊡ id⟷₂) rinv◎l
quote^₂ rinv◎r^ = !⟷₂ (_■_ ( (!-quote^₁ _) ⊡ id⟷₂) rinv◎l)
quote^₂ id⟷₂^ = id⟷₂
quote^₂ (_■^_ α α₁) = _■_ (quote^₂ α) (quote^₂ α₁)
quote^₂ (α ⊡^ α₁) = quote^₂ α ⊡ quote^₂ α₁
quote^₂ ⊕id⟷₁⟷₂^ = id⟷₁⊕id⟷₁⟷₂
quote^₂ !⊕id⟷₁⟷₂^ = split⊕-id⟷₁
quote^₂ hom◎⊕⟷₂^ = _■_ hom◎⊕⟷₂ (resp⊕⟷₂ idl◎l id⟷₂)
quote^₂ (resp⊕⟷₂ α) = resp⊕⟷₂ id⟷₂ (quote^₂ α)
quote^₂ hom⊕◎⟷₂^ = !⟷₂ (_■_ hom◎⊕⟷₂ (resp⊕⟷₂ idl◎l id⟷₂))
quote^₂ swapr₊⟷₂^ =
    _ ⟷₂⟨ assoc◎l ⟩
    _ ⟷₂⟨ assocl₊l ⊡ id⟷₂ ⟩
    _ ⟷₂⟨ assoc◎r ⟩
    _ ⟷₂⟨ id⟷₂ ⊡ assoc◎l ⟩
    _ ⟷₂⟨ id⟷₂ ⊡ (hom◎⊕⟷₂ ⊡ id⟷₂) ⟩
    _ ⟷₂⟨ id⟷₂ ⊡ (resp⊕⟷₂ swapr₊⟷₂ idl◎r ⊡ id⟷₂) ⟩
    _ ⟷₂⟨ id⟷₂ ⊡ (hom⊕◎⟷₂ ⊡ id⟷₂) ⟩
    _ ⟷₂⟨ id⟷₂ ⊡ assoc◎r ⟩
    _ ⟷₂⟨ id⟷₂ ⊡ (id⟷₂ ⊡ assocr₊r) ⟩
    _ ⟷₂⟨ assoc◎l ⟩
    _ ⟷₂⟨ assoc◎l ⟩
    _ ⟷₂⟨ assoc◎r ⊡ resp⊕⟷₂ id⟷₂ (resp⊕⟷₂ id⟷₂ idr◎l) ⟩
    _ ⟷₂∎
quote^₂ (swapl₊⟷₂^ {c = c}) =
    let r = (quote^₂ (swapr₊⟷₂^ {c = c}))
    in !⟷₂ r
quote^₂ hexagonl₊l =
    let s₁ = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
        s₂ = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
    in  s₁ ◎ (id⟷₁ ⊕ s₂) ◎ s₁          ⟷₂⟨ TODO! ⟩ -- last step in MacLane's CWM proof
        (id⟷₁ ⊕ s₂) ◎ s₁ ◎ (id⟷₁ ⊕ s₂) ⟷₂∎
quote^₂ hexagonl₊r =
    let r = (quote^₂ hexagonl₊l)
    in !⟷₂ r

eval^₂-O : {t₁ t₂ : U O} → (c : t₁ ⟷₁ t₂) → eval^₁ c ⟷₂^ id⟷₁^
eval^₂-O c = c₊⟷₂id⟷₁^ (eval^₁ c)

c₊⟷₂id⟷₁ : (c : O ⟷₁ O) → c ⟷₂ id⟷₁
c₊⟷₂id⟷₁ c = 
        let x = quote^₂ (eval^₂-O c)
        in  ((idr◎r ■ idl◎r) ■ !⟷₂ (quote-eval^₁ c)) ■ x

eval^₂ : {t₁ : U n} {t₂ : U m} {c₁ c₂ : t₁ ⟷₁ t₂} → c₁ ⟷₂ c₂ → eval^₁ c₁ ⟷₂^ eval^₁ c₂
eval^₂ assoc◎l = assoc◎l^
eval^₂ assoc◎r = assoc◎r^
eval^₂ {c₁ = cc₁} {c₂ = cc₂} (assocl₊r {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}) = 
    let e = resp!⟷₂ (!⟷₂^ (++^-assoc-⊕ {c₁ = eval^₁ (!⟷₁ c₁)} {c₂ = eval^₁ (!⟷₁ c₂)} {c₃ = eval^₁ (!⟷₁ c₃)}))
        r₁ = eval^₁-! c₁
        r₂ = eval^₁-! c₂
        r₃ = eval^₁-! c₃
        
        r-mx = ++^-⊕-◎ r₁ (++^-⊕-◎ r₂ r₃)
        r-!-lx = ++^-⊕-◎-r {c₁ = !⟷₁^ (eval^₁ c₁)} (++^-⊕-! (eval^₁ c₂) (eval^₁ c₃))
        r-!-rx = ++^-⊕-! (eval^₁ c₁) (++^-⊕ (eval^₁ c₂) (eval^₁ c₃))        
        r-!-mx = r-!-lx ■^ r-!-rx
        r-m = (resp!⟷₂ (r-mx ■^ r-!-mx)) ■^ !!⟷₁^ _

        l-mx = ++^-⊕-◎ (++^-⊕-◎ r₁ r₂) r₃ 
        l-!-lx = ++^-⊕-◎-l {c₃ = !⟷₁^ (eval^₁ c₃)} (++^-⊕-! (eval^₁ c₁) (eval^₁ c₂))
        l-!-rx = ++^-⊕-! (++^-⊕ (eval^₁ c₁) (eval^₁ c₂)) (eval^₁ c₃)
        l-!-mx = l-!-lx ■^ l-!-rx
        l-m = !⟷₂^ ((resp!⟷₂ (l-mx ■^ l-!-mx)) ■^ !!⟷₁^ _)

    in  (id⟷₂^ ⊡^  l-m) ■^ e ■^ (r-m ⊡^ id⟷₂^)
eval^₂ (assocl₊l {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}) = 
    let e = resp!⟷₂ (!⟷₂^ (++^-assoc-⊕ {c₁ = eval^₁ (!⟷₁ c₁)} {c₂ = eval^₁ (!⟷₁ c₂)} {c₃ = eval^₁ (!⟷₁ c₃)}))
        r₁ = eval^₁-! c₁
        r₂ = eval^₁-! c₂
        r₃ = eval^₁-! c₃
        
        r-mx = ++^-⊕-◎ r₁ (++^-⊕-◎ r₂ r₃)
        r-!-lx = ++^-⊕-◎-r {c₁ = !⟷₁^ (eval^₁ c₁)} (++^-⊕-! (eval^₁ c₂) (eval^₁ c₃))
        r-!-rx = ++^-⊕-! (eval^₁ c₁) (++^-⊕ (eval^₁ c₂) (eval^₁ c₃))        
        r-!-mx = r-!-lx ■^ r-!-rx
        r-m = (resp!⟷₂ (r-mx ■^ r-!-mx)) ■^ !!⟷₁^ _

        l-mx = ++^-⊕-◎ (++^-⊕-◎ r₁ r₂) r₃ 
        l-!-lx = ++^-⊕-◎-l {c₃ = !⟷₁^ (eval^₁ c₃)} (++^-⊕-! (eval^₁ c₁) (eval^₁ c₂))
        l-!-rx = ++^-⊕-! (++^-⊕ (eval^₁ c₁) (eval^₁ c₂)) (eval^₁ c₃)
        l-!-mx = l-!-lx ■^ l-!-rx
        l-m = !⟷₂^ ((resp!⟷₂ (l-mx ■^ l-!-mx)) ■^ !!⟷₁^ _)
    in  !⟷₂^ ((id⟷₂^ ⊡^  l-m) ■^ e ■^ (r-m ⊡^ id⟷₂^))
eval^₂ (assocr₊r {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}) = !⟷₂^ (++^-assoc-⊕ {c₁ = eval^₁ c₁} {c₂ = eval^₁ c₂} {c₃ = eval^₁ c₃})
eval^₂ (assocr₊l {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}) = ++^-assoc-⊕ {c₁ = eval^₁ c₁} {c₂ = eval^₁ c₂} {c₃ = eval^₁ c₃}
eval^₂ idl◎l = idl◎l^
eval^₂ idl◎r = idl◎r^
eval^₂ idr◎l = idr◎l^
eval^₂ idr◎r = idr◎r^
eval^₂ (linv◎l {c = c}) = (id⟷₂^ ⊡^ eval^₁-! c) ■^ linv◎l^
eval^₂ (linv◎r {c = c}) = linv◎r^ ■^ (id⟷₂^ ⊡^ !⟷₂^ (eval^₁-! c))
eval^₂ (rinv◎l {c = c}) = (eval^₁-! c ⊡^ id⟷₂^) ■^ rinv◎l^
eval^₂ (rinv◎r {c = c}) = rinv◎r^ ■^ (!⟷₂^ (eval^₁-! c) ⊡^ id⟷₂^)
eval^₂ (unite₊l⟷₂l {c₁ = c₁}) with (c₊⟷₂id⟷₁ c₁)
... | α =  !⟷₂^ (idr◎l^ ■^ (++^-⊕-◎-l (eval^₂-O c₁)) ■^ idl◎r^)
eval^₂ (unite₊l⟷₂r {c₁ = c₁}) with (c₊⟷₂id⟷₁ c₁)
... | α = (idr◎l^ ■^ (++^-⊕-◎-l (eval^₂-O c₁)) ■^ idl◎r^)
eval^₂ (uniti₊l⟷₂l {c₁ = c₁}) with (c₊⟷₂id⟷₁ c₁)
... | α = (idl◎l^ ■^ (++^-⊕-◎-l (eval^₂-O c₁)) ■^ idr◎r^)
eval^₂ (uniti₊l⟷₂r {c₁ = c₁}) with (c₊⟷₂id⟷₁ c₁)
... | α = !⟷₂^ (idl◎l^ ■^ (++^-⊕-◎-l (eval^₂-O c₁)) ■^ idr◎r^)
eval^₂ swapl₊⟷₂ = TODO! -- naturality of ++-swap
eval^₂ swapr₊⟷₂ = TODO! -- naturality of ++-swap
eval^₂ id⟷₂ = id⟷₂^
eval^₂ (_■_ α₁ α₂) = _■^_ (eval^₂ α₁) (eval^₂ α₂)
eval^₂ (α₁ ⊡ α₂) = eval^₂ α₁ ⊡^ eval^₂ α₂
eval^₂ (resp⊕⟷₂ α₁ α₂) = ++^-⊕-◎ (eval^₂ α₁) (eval^₂ α₂)
eval^₂ (id⟷₁⊕id⟷₁⟷₂ {n}) = ++^-⊕-id-l {n = _} {m = _} {o = n} (id⟷₁^ {n = _}) ■^ ++^-l-id
eval^₂ (split⊕-id⟷₁ {n}) = !⟷₂^ (++^-⊕-id-l {n = _} {m = _} {o = n} (id⟷₁^ {n = _}) ■^ ++^-l-id)
eval^₂ hom⊕◎⟷₂ = TODO- -- functoriality of ++^-⊕
eval^₂ hom◎⊕⟷₂ = TODO- -- functoriality of ++^-⊕
eval^₂ (triangle₊l {n}) =
    _ ⟷₂^⟨ (++^-⊕-id-r (++^-swap n 0)) ⊡^ ++^-⊕-id-r (id⟷₁^ {n}) ⟩
    _ ⟷₂^⟨ idr◎l^  ⟩
    _ ⟷₂^⟨ (++^-r⟷₂ (++^-swap-0 n)) ⟩
    _ ⟷₂^⟨ (++^-r⟷₂ (!!⟷₁^ (++^-unit-r n))) ⟩
    _ ⟷₂^⟨ !⟷₂^ (++^-triangle n _) ⟩
    _ ⟷₂^⟨ id⟷₂^ ⊡^ !⟷₂^ (++^-⊕-id-l id⟷₁^) ⟩
    _ ⟷₂^∎
eval^₂ (triangle₊r {n}) =
    _ ⟷₂^⟨ id⟷₂^ ⊡^ (++^-⊕-id-l id⟷₁^) ⟩
    _ ⟷₂^⟨ ++^-triangle n _  ⟩
    _ ⟷₂^⟨ !⟷₂^ (++^-r⟷₂ (!!⟷₁^ (++^-unit-r n))) ⟩
    _ ⟷₂^⟨ !⟷₂^ (++^-r⟷₂ (++^-swap-0 n)) ⟩
    _ ⟷₂^⟨ idr◎r^ ⟩
    _ ⟷₂^⟨ !⟷₂^ (++^-⊕-id-r (++^-swap n 0) ⊡^ ++^-⊕-id-r (id⟷₁^ {n})) ⟩
    _ ⟷₂^∎
eval^₂ (pentagon₊l {n₁} {t₁} {n₂} {t₂} {n₃} {t₃} {n₄} {t₄}) =
  ++^-pentagon n₁ n₂ n₃ n₄ ■^
  (!⟷₂^ (++^-⊕-id-r (++^-assoc n₁ n₂ n₃)) ⊡^ (id⟷₂^ ⊡^ !⟷₂^ (++^-⊕-id-l (++^-assoc n₂ n₃ n₄)))) ■^
  assoc◎l^
eval^₂ (pentagon₊r {n₁} {t₁} {n₂} {t₂} {n₃} {t₃} {n₄} {t₄}) =
  assoc◎r^ ■^
  (++^-⊕-id-r (++^-assoc n₁ n₂ n₃) ⊡^ (id⟷₂^ ⊡^ ++^-⊕-id-l (++^-assoc n₂ n₃ n₄))) ■^
  !⟷₂^ (++^-pentagon n₁ n₂ n₃ n₄)
eval^₂ (unite₊l-coh-l {t₁ = t₁}) =
  idl◎r^ ■^ (!⟷₂^ (++^-swap-unit (eval^₀ t₁)) ⊡^ id⟷₂^) ■^ assoc◎r^
eval^₂ (unite₊l-coh-r {t₁ = t₁}) =
  assoc◎l^ ■^ (++^-swap-unit (eval^₀ t₁) ⊡^ id⟷₂^) ■^ idl◎l^
eval^₂ hexagonr₊l = TODO!
eval^₂ hexagonr₊r = TODO!
eval^₂ hexagonl₊l = TODO!
eval^₂ hexagonl₊r = TODO!

