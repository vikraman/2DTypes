{-# OPTIONS --without-K  --rewriting #-}

module Pi+.Indexed.SyntaxHatHelpers where

open import HoTT hiding (_++_) renaming (_+_ to _++_)

open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.Extra

private
  variable
    n m o p : ℕ
    c c₁ c₂ : n ⟷₁^ m

++^-id : (n == m) → n ⟷₁^ m
++^-id p = transport (λ n → _ ⟷₁^ n) p id⟷₁^

-- ++^-id {O} {O} p = id⟷₁^
-- ++^-id {S n} {S m} p = ⊕^ (++^-id (ℕ-S-is-inj n m p))

++^-l : {n m o : ℕ} → (n ⟷₁^ m) → (o ++ n) ⟷₁^ (o ++ m)
++^-l {o = O} c = c
++^-l {o = S o} c = ⊕^ ++^-l c

++^-l-! : {o : ℕ} → (++^-l {o = o} (!⟷₁^ c)) ⟷₂^ !⟷₁^ (++^-l {o = o} c)
++^-l-! {o = O} = id⟷₂^
++^-l-! {o = S o} = resp⊕⟷₂ (++^-l-! {o = o})

++^-r : {n m o : ℕ} → (n ⟷₁^ m) → (n ++ o) ⟷₁^ (m ++ o)
++^-r swap₊^ = swap₊^
++^-r id⟷₁^ = id⟷₁^
++^-r (c₁ ◎^ c₂) = ++^-r c₁ ◎^ ++^-r c₂
++^-r (⊕^ c) = ⊕^ (++^-r c)
-- ++^-r c = ++^-id (⟷₁-size-eq c)

++^-r-! : {o : ℕ} → (++^-r {o = o} (!⟷₁^ c)) ⟷₂^ !⟷₁^ (++^-r {o = o} c)
++^-r-! {c = swap₊^} = id⟷₂^
++^-r-! {c = id⟷₁^} = id⟷₂^
++^-r-! {c = c ◎^ c₁} = ++^-r-! ⊡^ ++^-r-!
++^-r-! {c = ⊕^ c} = resp⊕⟷₂ ++^-r-!

++^-r⟷₂ : {o : ℕ} → (c₁ ⟷₂^ c₂) → (++^-r {o = o} c₁) ⟷₂^ ++^-r {o = o} c₂
++^-r⟷₂ assoc◎l^ = assoc◎l^
++^-r⟷₂ assoc◎r^ = assoc◎r^
++^-r⟷₂ idl◎l^ = idl◎l^
++^-r⟷₂ idl◎r^ = idl◎r^
++^-r⟷₂ idr◎l^ = idr◎l^
++^-r⟷₂ idr◎r^ = idr◎r^
++^-r⟷₂ linv◎l^ = (id⟷₂^ ⊡^ ++^-r-!) ■^ linv◎l^
++^-r⟷₂ linv◎r^ = !⟷₂^ ((id⟷₂^ ⊡^ ++^-r-!) ■^ linv◎l^)
++^-r⟷₂ rinv◎l^ = (++^-r-! ⊡^ id⟷₂^) ■^ rinv◎l^
++^-r⟷₂ rinv◎r^ = !⟷₂^ ((++^-r-! ⊡^ id⟷₂^) ■^ rinv◎l^)
++^-r⟷₂ id⟷₂^ = id⟷₂^
++^-r⟷₂ (α ■^ α₁) = ++^-r⟷₂ α ■^ ++^-r⟷₂ α₁
++^-r⟷₂ (α ⊡^ α₁) = ++^-r⟷₂ α ⊡^ ++^-r⟷₂ α₁
++^-r⟷₂ ⊕id⟷₁⟷₂^ = ⊕id⟷₁⟷₂^
++^-r⟷₂ !⊕id⟷₁⟷₂^ = !⊕id⟷₁⟷₂^
++^-r⟷₂ hom◎⊕⟷₂^ = hom◎⊕⟷₂^
++^-r⟷₂ (resp⊕⟷₂ α) = resp⊕⟷₂ (++^-r⟷₂ α)
++^-r⟷₂ hom⊕◎⟷₂^ = hom⊕◎⟷₂^
++^-r⟷₂ swapr₊⟷₂^ = swapr₊⟷₂^
++^-r⟷₂ swapl₊⟷₂^ = swapl₊⟷₂^
++^-r⟷₂ hexagonl₊l = hexagonl₊l
++^-r⟷₂ hexagonl₊r = hexagonl₊r

++^-unit-l : (n : ℕ) → O ++ n ⟷₁^ n
++^-unit-l n = id⟷₁^

++^-unit-r : (n : ℕ) → n ++ O ⟷₁^ n
++^-unit-r O = id⟷₁^
++^-unit-r (S n) = ⊕^ (++^-unit-r n)

++^-assoc : (n m o : ℕ) → (n ++ m) ++ o ⟷₁^ n ++ (m ++ o)
++^-assoc O m o = id⟷₁^
++^-assoc (S n) m o = ⊕^ ++^-assoc n m o

++^-cons : (n : ℕ) → (S n) ⟷₁^ (n ++ 1)
++^-cons O = id⟷₁^
++^-cons (S n) = swap₊^ ◎^ (⊕^ (++^-cons n))

++^-swap : (n m : ℕ) → (n ++ m) ⟷₁^ (m ++ n)
++^-swap O m = !⟷₁^ (++^-unit-r m)
++^-swap (S n) m = (⊕^ ++^-swap n m)
                 ◎^ ++^-cons (m ++ n)
                 ◎^ ++^-assoc m n 1
                 ◎^ !⟷₁^ (++^-l (++^-cons n))

++^-swap-0 : (n : ℕ) → (++^-swap n 0) ⟷₂^ !⟷₁^ (++^-swap 0 n)
++^-swap-0 O = id⟷₂^
++^-swap-0 (S n) =
  let r = ++^-swap-0 n
  in  ((resp⊕⟷₂ r) ⊡^ id⟷₂^) ■^
      ((id⟷₂^ ⊡^ (id⟷₂^ ⊡^ idl◎l^)) ■^
      ((id⟷₂^ ⊡^ linv◎l^) ■^
      idr◎l^))

++^-⊕ : {n m o p : ℕ} → (n ⟷₁^ m) → (o ⟷₁^ p) → (n ++ o) ⟷₁^ (m ++ p)
++^-⊕ (swap₊^ {n = n}) c₂ = big-swap₊^ (++^-⊕ id⟷₁^ c₂)
++^-⊕ {O} id⟷₁^ c₂ = c₂
++^-⊕ {S n} id⟷₁^ c₂ = ⊕^ (++^-⊕ {n} id⟷₁^ c₂)
++^-⊕ (c₁ ◎^ c₃) c₂ = (++^-⊕ c₁ c₂) ◎^ ++^-⊕ c₃ id⟷₁^
++^-⊕ (⊕^ c₁) c₂ = ⊕^ (++^-⊕ c₁ c₂)
-- FIXME can we define it as follows?
-- ++^-⊕ {n} {m} {o} {p} c₁ c₂ with ⟷₁^-eq-size c₁
-- ... | idp = ++^-l c₂

++^-⊕-id-r : {n m o : ℕ} → (c : n ⟷₁^ m) → (++^-⊕ c (id⟷₁^ {o})) ⟷₂^ ++^-r c
++^-⊕-id-r swap₊^ = id⟷₂^
++^-⊕-id-r {O} id⟷₁^ = id⟷₂^
++^-⊕-id-r {S n} id⟷₁^ = resp⊕⟷₂ (++^-⊕-id-r {n} id⟷₁^) ■^ ⊕id⟷₁⟷₂^
++^-⊕-id-r (c₁ ◎^ c₂) = ++^-⊕-id-r c₁ ⊡^ ++^-⊕-id-r c₂
++^-⊕-id-r (⊕^ c) = resp⊕⟷₂ (++^-⊕-id-r c)

++^-⊕-id-l : (c : n ⟷₁^ m) → (++^-⊕ (id⟷₁^ {n = o}) c) ⟷₂^ (++^-l {o = o} c)
++^-⊕-id-l {o = O} c = id⟷₂^
++^-⊕-id-l {o = S o} c = resp⊕⟷₂ (++^-⊕-id-l {o = o} c)

++^-⊕-! : {n m o p : ℕ} → (c₁ : n ⟷₁^ m) (c₂ : o ⟷₁^ p)
        → (++^-⊕ (!⟷₁^ c₁) (!⟷₁^ c₂)) ⟷₂^ (!⟷₁^ (++^-⊕ c₁ c₂))
++^-⊕-! swap₊^ c₂ with (⟷₁^-eq-size c₂)
... | idp = id⟷₂^
++^-⊕-! id⟷₁^ c₂ =
  ++^-⊕-id-l (!⟷₁^ c₂) ■^
  (++^-l-! {c = c₂} ■^ resp!⟷₂ (!⟷₂^ (++^-⊕-id-l c₂)))
++^-⊕-! (c₁ ◎^ c₃) c₂ =
  (++^-⊕-! c₃ c₂ ⊡^ ++^-⊕-id-r (!⟷₁^ c₁)) ■^
  (id⟷₂^ ⊡^ ++^-r-!) ■^
  TODO-
++^-⊕-! (⊕^ c₁) c₂ = resp⊕⟷₂ (++^-⊕-! c₁ c₂)

++^-⊕-◎-l : {n m o p : ℕ} {c₁ c₂ : n ⟷₁^ m} {c₃ : o ⟷₁^ p} (α : c₁ ⟷₂^ c₂)
          → (++^-⊕ c₁ c₃) ⟷₂^ (++^-⊕ c₂ c₃)
++^-⊕-◎-l α = TODO-

++^-⊕-◎-r : {n m o p : ℕ} → {c₁ : n ⟷₁^ m} {c₂ c₃ : o ⟷₁^ p} (α : c₂ ⟷₂^ c₃)
          → (++^-⊕ c₁ c₂) ⟷₂^ (++^-⊕ c₁ c₃)
++^-⊕-◎-r α = TODO-

++^-⊕-◎ : {n m o p : ℕ} → {c₁ c₂ : n ⟷₁^ m} {c₃ c₄ : o ⟷₁^ p} (α : c₁ ⟷₂^ c₂) (β : c₃ ⟷₂^ c₄)
        → (++^-⊕ c₁ c₃) ⟷₂^ (++^-⊕ c₂ c₄)
++^-⊕-◎ α = TODO-

++^-triangle : (n m : ℕ)
             → (++^-assoc n O m) ◎^ ++^-l (++^-unit-l m) ⟷₂^ ++^-r (++^-unit-r n)
++^-triangle O m = idl◎l^
++^-triangle (S n) m = hom◎⊕⟷₂^ ■^ resp⊕⟷₂ (++^-triangle n m)

++^-pentagon : (n m o p : ℕ)
             → (++^-assoc (n ++ m) o p) ◎^ ++^-assoc n m (o ++ p) ⟷₂^
               ++^-r (++^-assoc n m o) ◎^ ++^-assoc n (m ++ o) p ◎^ ++^-l {o = n} (++^-assoc m o p)
++^-pentagon O m o p = idr◎r^ □^ idl◎l^ □^ idr◎r^ □^ idl◎l^ □^ (idr◎l^ ■^ (idr◎l^ ■^ idr◎l^))
++^-pentagon (S n) m o p =
  hom◎⊕⟷₂^ ■^ (resp⊕⟷₂ (++^-pentagon n m o p) ■^
  ((!⟷₂^ hom◎⊕⟷₂^) ■^ (id⟷₂^ ⊡^ hom⊕◎⟷₂^)))

++^-cons-assoc : (n m : ℕ) → ++^-r {o = m} (++^-cons n) ◎^ ++^-assoc n 1 m ⟷₂^ ++^-cons (n ++ m) ◎^ ++^-assoc n m 1 ◎^ !⟷₁^ (++^-l {o = n} (++^-cons m))
++^-cons-assoc O m = TODO-
++^-cons-assoc (S n) m = TODO-

-- c₁ = ⊕^ ++^-swap n (m ++ o)
-- c₂ = ++^-⊕ (++^-cons (m ++ o)) (id⟷₁^ {n})
-- c = c₁ ◎^ c₂

-- d₁ = ++^-⊕ (++^-swap (S n) m) (id⟷₁^ {o})
-- d₂ = ++^-⊕ (id⟷₁^ {m}) (++^-swap (S n) o)
-- d = d₁ ◎^ ++^-assoc m (S n) o ◎^ d₂

-- lemma : (++^-l {o = 1 ++ m} (++^-swap n o)) ◎^ ++^-r {o = n} (++^-cons (m ++ o)) ⟷₂^
--   (++^-r {o = n ++ o} (++^-cons m)) ◎^ (++^-l {o = m ++ 1} (++^-swap n o)) ◎^ (++^-l {o = m} (++^-r {o = n} (++^-cons o)))

++^-hexagon : (n m o : ℕ)
            → (++^-assoc n m o) ◎^ ++^-swap n (m ++ o) ◎^ ++^-assoc m o n ⟷₂^
              ++^-r {o = o} (++^-swap n m) ◎^ ++^-assoc m n o ◎^ ++^-l {o = m} (++^-swap n o)
++^-hexagon O m o = TODO!
++^-hexagon (S n) m o =
  let r = ++^-hexagon n m o
  in  _ ◎^ ((_ ◎^ (_ ◎^ (_ ◎^ _))) ◎^ _)  ⟷₂^⟨ id⟷₂^ ⊡^ assoc◎r^ ⟩
      _ ◎^ (_ ◎^ (_ ◎^ (_ ◎^ _)) ◎^ _) ⟷₂^⟨ assoc◎l^ ⟩
      (_ ◎^ _) ◎^ ((_ ◎^ (_ ◎^ _)) ◎^ _) ⟷₂^⟨ idr◎r^ ⊡^ id⟷₂^ ⟩
      ((_ ◎^ _ ) ◎^ id⟷₁^) ◎^ ((_ ◎^ (_ ◎^ _)) ◎^ _) ⟷₂^⟨ (id⟷₂^ ⊡^ linv◎r^ {c = ⊕^ (++^-assoc m o n)}) ⊡^ id⟷₂^ ⟩
      ((_ ◎^ _ ) ◎^ (_ ◎^ _)) ◎^ ((_ ◎^ (_ ◎^ _)) ◎^ _) ⟷₂^⟨ (hom◎⊕⟷₂^ ⊡^ hom◎⊕⟷₂^) ⊡^ id⟷₂^ ⟩
      ((⊕^ (_ ◎^ _ )) ◎^ (⊕^ (_ ◎^ _))) ◎^ ((_ ◎^ (_ ◎^ _)) ◎^ _) ⟷₂^⟨ hom◎⊕⟷₂^ ⊡^ id⟷₂^ ⟩
      (⊕^ ((_ ◎^ _ ) ◎^ (_ ◎^ _))) ◎^ ((_ ◎^ (_ ◎^ _)) ◎^ _) ⟷₂^⟨ resp⊕⟷₂ assoc◎l^ ⊡^ id⟷₂^ ⟩
      (⊕^ (((_ ◎^ _ ) ◎^ _) ◎^ _)) ◎^ ((_ ◎^ (_ ◎^ _)) ◎^ _) ⟷₂^⟨ (resp⊕⟷₂ (assoc◎r^ ⊡^ id⟷₂^)) ⊡^ id⟷₂^ ⟩
      (⊕^ ((_ ◎^ (_ ◎^ _)) ◎^ _)) ◎^ ((_ ◎^ (_ ◎^ _)) ◎^ _) ⟷₂^⟨ resp⊕⟷₂ (++^-hexagon n m o ⊡^ id⟷₂^) ⊡^ id⟷₂^ ⟩
      _ ⟷₂^⟨ TODO! ⟩
      _ ⟷₂^∎

  --     c₁ = ⊕^ ++^-swap n (m ++ o)
  --     c₂ = ++^-⊕ (++^-cons (m ++ o)) (id⟷₁^ {n})
  --     c = c₁ ◎^ c₂

  --     d₁ = ++^-⊕ (++^-swap (S n) m) (id⟷₁^ {o})
  --     d₂ = ++^-⊕ (id⟷₁^ {m}) (++^-swap (S n) o)
  --     d = d₁ ◎^ ++^-assoc m (S n) o ◎^ d₂
  -- in  {!   !}
  -- in  {!   !} ⟷₂^⟨ {!   !} ⟩
  --     (⊕^ ++^-assoc n m o) ◎^ (d ◎^ ++^-assoc (m ++ o) 1 n ◎^ ++^-assoc m o (1 ++ n)) ⟷₂^⟨ {!   !} ⟩
  --     c ⟷₂^⟨ {!   !} ⟩
  --     {!   !} ⟷₂^∎

-- ++^-hexagon O O o = idl◎l^ □^ idl◎l^ □^ idr◎l^ □^ idl◎l^
-- ++^-hexagon O (S m) o = {!   !}
-- ++^-hexagon (S n) m o = TODO!

++^-swap-unit : (n : ℕ) → !⟷₁^ (++^-unit-r n) ◎^ ++^-swap n 0 ⟷₂^ id⟷₁^
++^-swap-unit O = idl◎l^
++^-swap-unit (S n) =
  assoc◎l^ ■^
  ((!⟷₂^ hom⊕◎⟷₂^ ⊡^ (assoc◎l^ ■^ ((idr◎l^ ⊡^ id⟷₂^) ■^ linv◎l^))) ■^
    (idr◎l^ ■^ !⟷₂^ (!⊕id⟷₁⟷₂^ ■^ resp⊕⟷₂ (!⟷₂^ (++^-swap-unit n)))))

++^-symm-O : (n : ℕ) → ++^-swap O n ◎^ ++^-swap n O ⟷₂^ id⟷₁^
++^-symm-O O = idl◎l^
++^-symm-O (S n) = ++^-swap-unit (S n)

++^-swap-S-assoc : (n m : ℕ)
                 → ++^-swap (S n) m  ◎^ ++^-l {o = m} (++^-swap 1 n)  ⟷₂^
                   (⊕^ ++^-swap n m) ◎^ ++^-swap 1 (m ++ n) ◎^ (++^-assoc m n 1)
++^-swap-S-assoc n m = TODO!

++^-symm : (n m : ℕ) → ++^-swap n m ◎^ ++^-swap m n ⟷₂^ id⟷₁^
++^-symm O m = ++^-symm-O m
++^-symm (S n) m = TODO!
