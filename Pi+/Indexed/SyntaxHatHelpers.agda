{-# OPTIONS --without-K  --rewriting #-}

module Pi+.Indexed.SyntaxHatHelpers where

open import HoTT hiding (_++_) renaming (_+_ to _++_)

open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.Extra

private
  variable
    n m o p : ℕ

++^-id : (n == m) → n ⟷₁^ m
++^-id p = transport (λ n → _ ⟷₁^ n) p id⟷₁^

-- ++^-id {O} {O} p = id⟷₁^
-- ++^-id {S n} {S m} p = ⊕^ (++^-id (ℕ-S-is-inj n m p))

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

++^-⊕ : {n m o p : ℕ} → (n ⟷₁^ m) → (o ⟷₁^ p) → (n ++ o) ⟷₁^ (m ++ p)
++^-⊕ (swap₊^ {n = n}) c₂ = big-swap₊^ (++^-⊕ id⟷₁^ c₂)
++^-⊕ {O} id⟷₁^ c₂ = c₂
++^-⊕ {S n} id⟷₁^ c₂ = ⊕^ (++^-⊕ {n} id⟷₁^ c₂)
++^-⊕ (c₁ ◎^ c₃) c₂ = (++^-⊕ c₁ c₂) ◎^ ++^-⊕ c₃ id⟷₁^
++^-⊕ (⊕^ c₁) c₂ = ⊕^ (++^-⊕ c₁ c₂)

++^-swap : (n m : ℕ) → (n ++ m) ⟷₁^ (m ++ n)
++^-swap O m = !⟷₁^ (++^-unit-r m)
++^-swap (S n) m = (⊕^ ++^-swap n m)
                 ◎^ ++^-cons (m ++ n)
                 ◎^ ++^-assoc m n 1
                 ◎^ ++^-⊕ id⟷₁^ (!⟷₁^ (++^-cons n))

++^-l : {n m o : ℕ} → (n ⟷₁^ m) → (o ++ n) ⟷₁^ (o ++ m)
++^-l {o = O} c = c
++^-l {o = S o} c = ⊕^ ++^-l c

++^-r : {n m o : ℕ} → (n ⟷₁^ m) → (n ++ o) ⟷₁^ (m ++ o)
++^-r swap₊^ = swap₊^
++^-r id⟷₁^ = id⟷₁^
++^-r (c₁ ◎^ c₂) = ++^-r c₁ ◎^ ++^-r c₂
++^-r (⊕^ c) = ⊕^ (++^-r c)

++^-triangle : (n m : ℕ)
             → (++^-assoc n O m) ◎^ ++^-l (++^-unit-l m) ⟷₂^ ++^-r (++^-unit-r n)
++^-triangle O m = idl◎l^
++^-triangle (S n) O = TODO!
++^-triangle (S n) (S m) = TODO!

++^-pentagon : (n m o p : ℕ)
             → (++^-assoc (n ++ m) o p) ◎^ ++^-assoc n m (o ++ p) ⟷₂^
               ++^-r (++^-assoc n m o) ◎^ ++^-assoc n (m ++ o) p ◎^ ++^-⊕ (id⟷₁^ {n = n}) (++^-assoc m o p)
++^-pentagon O O o p = idl◎l^ □^ idl◎l^ □^ idl◎r^
++^-pentagon O (S m) o p = idl◎r^ □^ idl◎l^ □^  idl◎l^ □^ idl◎l^ □^ idr◎l^
++^-pentagon (S n) m o p = TODO!

++^-hexagon : (n m o : ℕ)
            → (++^-assoc n m o) ◎^ ++^-swap n (m ++ o) ◎^ ++^-assoc m o n ⟷₂^
              ++^-⊕ (++^-swap n m) (id⟷₁^ {n = o}) ◎^ ++^-assoc m n o ◎^ ++^-⊕ (id⟷₁^ {n = m}) (++^-swap n o)
++^-hexagon O O o = idl◎l^ □^ idl◎l^ □^ idl◎r^ □^ idl◎l^ □^ idl◎l^ □^ idr◎r^
++^-hexagon O (S m) o = TODO!
++^-hexagon (S n) m o = TODO!
