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
++^-r⟷₂ {c₁ = .(_ ◎^ _ ◎^ _)} {.((_ ◎^ _) ◎^ _)} assoc◎l^ = assoc◎l^
++^-r⟷₂ {c₁ = .((_ ◎^ _) ◎^ _)} {.(_ ◎^ _ ◎^ _)} assoc◎r^ = assoc◎r^
++^-r⟷₂ {c₁ = .(id⟷₁^ ◎^ c₂)} {c₂} idl◎l^ = idl◎l^
++^-r⟷₂ {c₁ = c₁} {.(id⟷₁^ ◎^ c₁)} idl◎r^ = idl◎r^
++^-r⟷₂ {c₁ = .(c₂ ◎^ id⟷₁^)} {c₂} idr◎l^ = idr◎l^
++^-r⟷₂ {c₁ = c₁} {.(c₁ ◎^ id⟷₁^)} idr◎r^ = idr◎r^
++^-r⟷₂ {c₁ = .(_ ◎^ !⟷₁^ _)} {.id⟷₁^} linv◎l^ = (id⟷₂^ ⊡^ ++^-r-!) ■^ linv◎l^
++^-r⟷₂ {c₁ = .id⟷₁^} {.(_ ◎^ !⟷₁^ _)} linv◎r^ = !⟷₂^ ((id⟷₂^ ⊡^ ++^-r-!) ■^ linv◎l^)
++^-r⟷₂ {c₁ = .(!⟷₁^ _ ◎^ _)} {.id⟷₁^} rinv◎l^ = (++^-r-! ⊡^ id⟷₂^) ■^ rinv◎l^
++^-r⟷₂ {c₁ = .id⟷₁^} {.(!⟷₁^ _ ◎^ _)} rinv◎r^ = !⟷₂^ ((++^-r-! ⊡^ id⟷₂^) ■^ rinv◎l^)
++^-r⟷₂ {c₁ = c₁} {.c₁} id⟷₂^ = id⟷₂^
++^-r⟷₂ {c₁ = c₁} {c₂} (α ■^ α₁) = ++^-r⟷₂ α ■^ ++^-r⟷₂ α₁
++^-r⟷₂ {c₁ = .(_ ◎^ _)} {.(_ ◎^ _)} (α ⊡^ α₁) = ++^-r⟷₂ α ⊡^ ++^-r⟷₂ α₁
++^-r⟷₂ {c₁ = .(⊕^ id⟷₁^)} {.id⟷₁^} ⊕id⟷₁⟷₂^ = ⊕id⟷₁⟷₂^
++^-r⟷₂ {c₁ = .id⟷₁^} {.(⊕^ id⟷₁^)} !⊕id⟷₁⟷₂^ = !⊕id⟷₁⟷₂^
++^-r⟷₂ {c₁ = .((⊕^ _) ◎^ ⊕^ _)} {.(⊕^ _ ◎^ _)} hom◎⊕⟷₂^ = hom◎⊕⟷₂^
++^-r⟷₂ {c₁ = .(⊕^ _)} {.(⊕^ _)} (resp⊕⟷₂ α) = resp⊕⟷₂ (++^-r⟷₂ α)
++^-r⟷₂ {c₁ = .(⊕^ _ ◎^ _)} {.((⊕^ _) ◎^ ⊕^ _)} hom⊕◎⟷₂^ = hom⊕◎⟷₂^
++^-r⟷₂ {c₁ = .((⊕^ ⊕^ _) ◎^ swap₊^)} {.(swap₊^ ◎^ ⊕^ ⊕^ _)} swapr₊⟷₂^ = swapr₊⟷₂^
++^-r⟷₂ {c₁ = .(swap₊^ ◎^ ⊕^ ⊕^ _)} {.((⊕^ ⊕^ _) ◎^ swap₊^)} swapl₊⟷₂^ = swapl₊⟷₂^
++^-r⟷₂ {c₁ = .(swap₊^ ◎^ (⊕^ swap₊^) ◎^ swap₊^)} {.((⊕^ swap₊^) ◎^ swap₊^ ◎^ ⊕^ swap₊^)} hexagonl₊l = hexagonl₊l
++^-r⟷₂ {c₁ = .((⊕^ swap₊^) ◎^ swap₊^ ◎^ ⊕^ swap₊^)} {.(swap₊^ ◎^ (⊕^ swap₊^) ◎^ swap₊^)} hexagonl₊r = hexagonl₊r

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
