{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Level0 where

open import lib.Base
open import lib.PathGroupoid
open import lib.types.Nat renaming (_+_ to _+ℕ_)
open import lib.types.Sigma

-----------------------------------------------------------------------------
-- Pi extended with special id combinators

data U : Set where
  O I : U
  _+_ : U → U → U

∣_∣ : U → ℕ
∣ O ∣ = 0
∣ I ∣ = 1
∣ t₁ + t₂ ∣ = ∣ t₁ ∣ +ℕ ∣ t₂ ∣

⟪_⟫ : ℕ → U
⟪ O ⟫ = O
⟪ S n ⟫ = I + ⟪ n ⟫

-- Canonical representation of sum types as lists I + (I + (I + ... O))

canonU : U → U
canonU t = ⟪ ∣ t ∣ ⟫

∣⟪⟫∣ : (n : ℕ) → ∣ ⟪ n ⟫ ∣ == n
∣⟪⟫∣ O = idp
∣⟪⟫∣ (S n) = ap S (∣⟪⟫∣ n)

canon-invol : (t : U) → canonU (canonU t) == canonU t
canon-invol t = ap ⟪_⟫ (∣⟪⟫∣ ∣ t ∣)

canonU-assoc : (t₁ t₂ t₃ : U) →
  canonU (t₁ + (t₂ + t₃)) == canonU ((t₁ + t₂) + t₃)
canonU-assoc t₁ t₂ t₃ rewrite +-assoc (∣ t₁ ∣) (∣ t₂ ∣) (∣ t₃ ∣) = idp

infixr 40 _+_
infix 30 _⟷₁_
infixr 50 _◎_ _⊕_

data _⟷₁_  : U → U → Set where
  unite₊l : {t : U} → O + t ⟷₁ t
  uniti₊l : {t : U} → t ⟷₁ O + t
  swap₊   : {t₁ t₂ : U} → t₁ + t₂ ⟷₁ t₂ + t₁
  assocl₊ : {t₁ t₂ t₃ : U} → t₁ + (t₂ + t₃) ⟷₁ (t₁ + t₂) + t₃
  assocr₊ : {t₁ t₂ t₃ : U} → (t₁ + t₂) + t₃ ⟷₁ t₁ + (t₂ + t₃)
  id⟷₁    : {t : U} → t ⟷₁ t
  idupto⟷₁ : {t₁ t₂ : U} → {canonU t₁ == canonU t₂} → t₁ ⟷₁ t₂
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷₁ t₂) → (t₂ ⟷₁ t₃) → (t₁ ⟷₁ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} → (t₁ ⟷₁ t₃) → (t₂ ⟷₁ t₄) → (t₁ + t₂ ⟷₁ t₃ + t₄)

-- Definitional inverse

!⟷₁ : {t₁ t₂ : U} → t₁ ⟷₁ t₂ → t₂ ⟷₁ t₁
!⟷₁ unite₊l = uniti₊l
!⟷₁ uniti₊l = unite₊l
!⟷₁ swap₊ = swap₊
!⟷₁ assocl₊ = assocr₊
!⟷₁ assocr₊ = assocl₊
!⟷₁ id⟷₁ = id⟷₁
!⟷₁ (idupto⟷₁ {t₁} {t₂} {eq}) = idupto⟷₁ {t₂} {t₁} { ! eq }
!⟷₁ (c₁ ◎ c₂) = !⟷₁ c₂ ◎ !⟷₁ c₁
!⟷₁ (c₁ ⊕ c₂) = !⟷₁ c₁ ⊕ !⟷₁ c₂

-- Equational reasoning

infixr 10 _⟷₁⟨_⟩_
infix  15 _⟷₁∎

_⟷₁⟨_⟩_ : ∀ {t₂ t₃ : U} → (t₁ : U) → (t₁ ⟷₁ t₂) → (t₂ ⟷₁ t₃) → (t₁ ⟷₁ t₃)
_ ⟷₁⟨ c₁ ⟩ c₂ = c₁ ◎ c₂

_⟷₁∎ : (t : U) → t ⟷₁ t
_⟷₁∎ t = id⟷₁

-- Level 2

data _⟷₂_ : {X Y : U} → X ⟷₁ Y → X ⟷₁ Y → Set where
  assoc◎l : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₃ ⟷₁ t₄} →
          (c₁ ◎ (c₂ ◎ c₃)) ⟷₂ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₃ ⟷₁ t₄} →
          ((c₁ ◎ c₂) ◎ c₃) ⟷₂ (c₁ ◎ (c₂ ◎ c₃))
  assocl₊l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊) ⟷₂ (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃))
  assocl₊r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃)) ⟷₂ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊)
  assocr₊r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
          (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⟷₂ (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃)))
  assocr₊l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₅ ⟷₁ t₆} →
           (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))) ⟷₂ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
  idl◎l   : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → (id⟷₁ ◎ c) ⟷₂ c
  idl◎r   : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → c ⟷₂ id⟷₁ ◎ c
  idr◎l   : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → (c ◎ id⟷₁) ⟷₂ c
  idr◎r   : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → c ⟷₂ (c ◎ id⟷₁)
  linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → (c ◎ !⟷₁ c) ⟷₂ id⟷₁
  linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → id⟷₁ ⟷₂ (c ◎ !⟷₁ c)
  rinv◎l  : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → (!⟷₁ c ◎ c) ⟷₂ id⟷₁
  rinv◎r  : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → id⟷₁ ⟷₂ (!⟷₁ c ◎ c)
  unite₊l⟷₂l : {t₁ t₂ : U} {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          (unite₊l ◎ c₂) ⟷₂ ((c₁ ⊕ c₂) ◎ unite₊l)
  unite₊l⟷₂r : {t₁ t₂ : U} {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          ((c₁ ⊕ c₂) ◎ unite₊l) ⟷₂ (unite₊l ◎ c₂)
  uniti₊l⟷₂l : {t₁ t₂ : U} {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          (uniti₊l ◎ (c₁ ⊕ c₂)) ⟷₂ (c₂ ◎ uniti₊l)
  uniti₊l⟷₂r : {t₁ t₂ : U} {c₁ : O ⟷₁ O} {c₂ : t₁ ⟷₁ t₂} →
          (c₂ ◎ uniti₊l) ⟷₂ (uniti₊l ◎ (c₁ ⊕ c₂))
  swapl₊⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} →
          (swap₊ ◎ (c₁ ⊕ c₂)) ⟷₂ ((c₂ ⊕ c₁) ◎ swap₊)
  swapr₊⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} →
          ((c₂ ⊕ c₁) ◎ swap₊) ⟷₂ (swap₊ ◎ (c₁ ⊕ c₂))
  id⟷₂     : {t₁ t₂ : U} {c : t₁ ⟷₁ t₂} → c ⟷₂ c
  trans⟷₂  : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷₁ t₂} →
         (c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₃) → (c₁ ⟷₂ c₃)
  _⊡_  : {t₁ t₂ t₃ : U}
         {c₁ : t₁ ⟷₁ t₂} {c₂ : t₂ ⟷₁ t₃} {c₃ : t₁ ⟷₁ t₂} {c₄ : t₂ ⟷₁ t₃} →
         (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ◎ c₂) ⟷₂ (c₃ ◎ c₄)
  resp⊕⟷₂  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷₁ t₂} {c₂ : t₃ ⟷₁ t₄} {c₃ : t₁ ⟷₁ t₂} {c₄ : t₃ ⟷₁ t₄} →
         (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ⊕ c₂) ⟷₂ (c₃ ⊕ c₄)
  id⟷₁⊕id⟷₁⟷₂ : {t₁ t₂ : U} → (id⟷₁ {t₁} ⊕ id⟷₁ {t₂}) ⟷₂ id⟷₁
  split⊕-id⟷₁ : {t₁ t₂ : U} → (id⟷₁ {t₁ + t₂}) ⟷₂ (id⟷₁ ⊕ id⟷₁)
  hom⊕◎⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷₁ t₁} {c₂ : t₆ ⟷₁ t₂}
        {c₃ : t₁ ⟷₁ t₃} {c₄ : t₂ ⟷₁ t₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⟷₂ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷₁ t₁} {c₂ : t₆ ⟷₁ t₂}
        {c₃ : t₁ ⟷₁ t₃} {c₄ : t₂ ⟷₁ t₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⟷₂ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
  triangle⊕l : {t₁ t₂ : U} →
    unite₊l ⟷₂ assocl₊ {O} {t₁} {t₂} ◎ (unite₊l ⊕ id⟷₁)
  triangle⊕r : {t₁ t₂ : U} →
    assocl₊ {O} {t₁} {t₂} ◎ (unite₊l ⊕ id⟷₁) ⟷₂ unite₊l

-----------------------------------------------------------------------------
-- Converting Pi types to normal form

-- Append two lists of the form I + (I + ... O)
⟪++⟫ : {m n : ℕ} → ⟪ m ⟫ + ⟪ n ⟫ ⟷₁ ⟪ m +ℕ n ⟫
⟪++⟫ {O} = unite₊l
⟪++⟫ {S m} = assocr₊ ◎ (id⟷₁ ⊕ ⟪++⟫)

-- Flatten a Pi type (a tree) to a list
normC : (t : U) → t ⟷₁ canonU t
normC O = id⟷₁
normC I  = uniti₊l ◎ swap₊
normC (t₁ + t₂) = (normC t₁ ⊕ normC t₂) ◎ ⟪++⟫

-----------------------------------------------------------------------------
-- Define special combinators for canonical forms

data _⇔_ : (t₁ t₂ : U) → Set where
  id⇔ : {t₁ t₂ : U} → (canonU t₁ == canonU t₂) → canonU t₁ ⇔ canonU t₂
  seq⇔ : {t₁ t₂ t₃ : U} → (canonU t₁ ⇔ canonU t₂) → (canonU t₂ ⇔ canonU t₃) →
         (canonU t₁ ⇔ canonU t₃)
  bigswap⇔ : {t₁ t₂ : U} → canonU (t₁ + t₂) ⇔ canonU (t₂ + t₁)
  -- say | t₁ ∣ = 2 with elements {A,B} and ∣ t₂ = 3 ∣ with elements {C,D,E}, then
  -- canonU (t₁ + t₂) = (A + (B + (C + (D + (E + 0)))))
  -- the result of bigswap should be:
  -- (C + (D + (E + (A + (B + 0)))))
  -- below we express bigswap using a sequence of swaps
  bigplus⇔ : {t₁ t₂ t₃ t₄ : U} →
             (canonU t₁ ⇔ canonU t₃) → (canonU t₂ ⇔ canonU t₄) →
             (canonU (t₁ + t₂) ⇔ canonU (t₃ + t₄))
  -- say | t₁ ∣ = 2 with elements {A,B} and ∣ t₂ = 3 ∣ with elements {C,D,E}, then
  -- say c₁ maps (A + (B + 0)) to (X + (Y + 0))
  -- and c₂ maps (C + (D + (E + 0))) to (V + (W + (Z + 0)))
  -- we have canonU (t₁ + t₂) = (A + (B + (C + (D + (E + 0)))))
  -- the result of bigplus should be:
  -- (X + (Y + (V + (W + (Z + 0)))))

combNormalForm : {t₁ t₂ : U} → (c : t₁ ⟷₁ t₂) → (canonU t₁ ⇔ canonU t₂)
combNormalForm {t} id⟷₁ = id⇔ {t} {t} idp
combNormalForm (idupto⟷₁ {t₁} {t₂} {eq}) = id⇔ {t₁} {t₂} eq
combNormalForm {O + t} unite₊l = id⇔ {t} {t} idp
combNormalForm {t} uniti₊l = id⇔ {t} {t} idp
combNormalForm {t₁ + t₂} swap₊ = bigswap⇔ {t₁} {t₂}
combNormalForm {t₁ + (t₂ + t₃)} assocl₊ =
  id⇔ {t₁ + (t₂ + t₃)} {(t₁ + t₂) + t₃} (canonU-assoc t₁ t₂ t₃)
combNormalForm {(t₁ + t₂) + t₃} assocr₊ =
  id⇔ {(t₁ + t₂) + t₃} {t₁ + (t₂ + t₃)} (! (canonU-assoc t₁ t₂ t₃))
combNormalForm (_◎_ {t₁} {t₂} {t₃} c₁ c₂) =
  seq⇔ {t₁} {t₂} {t₃} (combNormalForm c₁) (combNormalForm c₂)
combNormalForm {t₁ + t₂} {t₃ + t₄} (c₁ ⊕ c₂) =
  bigplus⇔ {t₁} {t₂} {t₃} {t₄} (combNormalForm c₁) (combNormalForm c₂)

-----------------------------------------------------------------------------
-- Express special combinators as regular Pi combinators
-- Want these to be sequences of assocs and swaps

swapHead : {m : ℕ} → I + (I + ⟪ m ⟫) ⟷₁  I + (I + ⟪ m ⟫)
swapHead = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊

snoc : (m : ℕ) → ⟪ 1 +ℕ m ⟫ ⟷₁ ⟪ m +ℕ 1 ⟫
snoc O = id⟷₁
snoc (S n) = swapHead ◎ (id⟷₁ ⊕ snoc n)

dneppa : (m n : ℕ) → ⟪ m +ℕ n ⟫ ⟷₁ ⟪ n +ℕ m ⟫
dneppa O n = idupto⟷₁ {_} {_} {ap (λ X → canonU ⟪ X ⟫) (! (+-unit-r n))}
dneppa (S m) n =
  ⟪ S (m +ℕ n) ⟫
  ⟷₁⟨ snoc (m +ℕ n) ⟩
  ⟪ (m +ℕ n) +ℕ 1 ⟫
  ⟷₁⟨ idupto⟷₁ {_} {_} {ap (λ X → canonU ⟪ X ⟫) (+-assoc m n 1)} ⟩
  ⟪ m +ℕ (n +ℕ 1) ⟫
  ⟷₁⟨ dneppa m (n +ℕ 1) ⟩
  ⟪ (n +ℕ 1) +ℕ m ⟫
  ⟷₁⟨ idupto⟷₁ {_} {_} {ap (λ X → canonU ⟪ X ⟫) (+-assoc n 1 m)} ⟩
  ⟪ n +ℕ S m ⟫ ⟷₁∎

infix 100 _″

_″ : ∀ {t₁ t₂} → t₁ ⇔ t₂ → t₁ ⟷₁ t₂
(id⇔ eq) ″ = idupto⟷₁ {_} {_} {ap canonU eq}
seq⇔ c₁ c₂ ″ = c₁ ″ ◎ c₂ ″
bigplus⇔ c₁ c₂ ″ = !⟷₁ ⟪++⟫ ◎ (c₁ ″ ⊕ c₂ ″) ◎ ⟪++⟫
bigswap⇔ {t₁} {t₂} ″ = dneppa ∣ t₁ ∣ ∣ t₂ ∣

-----------------------------------------------------------------------------
-- Example

A1 A2 A3 A4 A5 A6 : U
A1 = I
A2 = I
A3 = I
A4 = I
A5 = I
A6 = I

tree : U
tree = ((A1 + A2) + A3) + ((A4 + A5) + A6)

mirrorTree : U
mirrorTree = (A6 + (A5 + A4)) + (A3 + (A2 + A1))

mirror : tree ⟷₁ mirrorTree
mirror = swap₊ ◎ (swap₊ ⊕ swap₊) ◎ ((id⟷₁ ⊕ swap₊) ⊕ (id⟷₁ ⊕ swap₊))

mirrorNF : canonU tree ⟷₁ canonU mirrorTree
mirrorNF = (combNormalForm mirror) ″

{--

(((assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
  id⟷₁ ⊕
  (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
  id⟷₁ ⊕
  (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
  id⟷₁ ⊕
  (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
  id⟷₁ ⊕ (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁ ⊕ id⟷₁)
 ◎
 idupto⟷₁ ◎
 (((assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
   id⟷₁ ⊕
   (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
   id⟷₁ ⊕
   (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
   id⟷₁ ⊕
   (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
   id⟷₁ ⊕ (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁ ⊕ id⟷₁)
  ◎
  idupto⟷₁ ◎
  (((assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
    id⟷₁ ⊕
    (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
    id⟷₁ ⊕
    (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
    id⟷₁ ⊕
    (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
    id⟷₁ ⊕ (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁ ⊕ id⟷₁)
   ◎ idupto⟷₁ ◎ idupto⟷₁ ◎ idupto⟷₁ ◎ id⟷₁)
  ◎ idupto⟷₁ ◎ id⟷₁)
 ◎ idupto⟷₁ ◎ id⟷₁)
◎
(((id⟷₁ ⊕ (id⟷₁ ⊕ (id⟷₁ ⊕ uniti₊l) ◎ assocl₊) ◎ assocl₊) ◎ assocl₊)
 ◎
 ((((assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
    id⟷₁ ⊕ (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁ ⊕ id⟷₁)
   ◎
   idupto⟷₁ ◎
   (((assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
     id⟷₁ ⊕ (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁ ⊕ id⟷₁)
    ◎ idupto⟷₁ ◎ idupto⟷₁ ◎ idupto⟷₁ ◎ id⟷₁)
   ◎ idupto⟷₁ ◎ id⟷₁)
  ⊕
  ((assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
   id⟷₁ ⊕ (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁ ⊕ id⟷₁)
  ◎
  idupto⟷₁ ◎
  (((assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
    id⟷₁ ⊕ (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁ ⊕ id⟷₁)
   ◎ idupto⟷₁ ◎ idupto⟷₁ ◎ idupto⟷₁ ◎ id⟷₁)
  ◎ idupto⟷₁ ◎ id⟷₁)
 ◎ assocr₊ ◎ id⟷₁ ⊕ assocr₊ ◎ id⟷₁ ⊕ assocr₊ ◎ id⟷₁ ⊕ unite₊l)
◎
((id⟷₁ ⊕ (id⟷₁ ⊕ (id⟷₁ ⊕ uniti₊l) ◎ assocl₊) ◎ assocl₊) ◎ assocl₊)
◎
((((id⟷₁ ⊕ uniti₊l) ◎ assocl₊) ◎
  (idupto⟷₁ ⊕
   ((assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁ ⊕ id⟷₁) ◎
   idupto⟷₁ ◎ idupto⟷₁ ◎ idupto⟷₁ ◎ id⟷₁)
  ◎ assocr₊ ◎ id⟷₁ ⊕ unite₊l)
 ⊕
 ((id⟷₁ ⊕ uniti₊l) ◎ assocl₊) ◎
 (idupto⟷₁ ⊕
  ((assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁ ⊕ id⟷₁) ◎
  idupto⟷₁ ◎ idupto⟷₁ ◎ idupto⟷₁ ◎ id⟷₁)
 ◎ assocr₊ ◎ id⟷₁ ⊕ unite₊l)
◎ assocr₊ ◎ id⟷₁ ⊕ assocr₊ ◎ id⟷₁ ⊕ assocr₊ ◎ id⟷₁ ⊕ unite₊l

--}

-----------------------------------------------------------------------------
-- Prove 2-equivalence between c and combNormalForm c

-----------------------------------------------------------------------------

{--

OLD STUFF. KEEP FOR NOW



<swap-big : (t₁ t₂ : U) → canonU (t₁ + t₂) ⟷₁ canonU (t₂ + t₁)
swap-big O t₂ = id⟷₁
swap-big I O = id⟷₁
swap-big I I = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
swap-big I (t₂ + t₃) =
  (id⟷₁ ⊕ !⟷₁ (⟪+⟫ ∣ t₂ ∣ ∣ t₃ ∣)) ◎
  assocl₊ ◎
  (swap-big I t₂ ⊕ id⟷₁) ◎
  (!⟷₁ (⟪+⟫ ∣ t₂ ∣ ∣ I ∣) ⊕ id⟷₁) ◎
  assocr₊ ◎
  {!!}
swap-big (t₁ + t₃) t₂ = {!!}

⟪+⟫-assoc : (m n k : ℕ) →
  (id⟷₁ ⊕ ⟪+⟫ n k) ◎ ⟪+⟫ m (n +ℕ k) ⟷₂
  assocl₊ ◎ (⟪+⟫ m n ⊕ id⟷₁) ◎ ⟪+⟫ (m +ℕ n) k
⟪+⟫-assoc O n k = trans⟷₂ unite₊l⟷₂r (trans⟷₂ (triangle⊕l ⊡ id⟷₂) assoc◎r)
⟪+⟫-assoc (S m) n k =
    ((id⟷₁ ⊕ ⟪+⟫ n k) ◎ assocr₊ ◎ (id⟷₁ ⊕ ⟪+⟫ m (n +ℕ k)))
  ⟷₂⟨ {!!} ⟩
    ((assocl₊ ◎ ((assocr₊ ◎ (id⟷₁ ⊕ ⟪+⟫ m n)) ⊕ id⟷₁)) ◎ (assocr₊ ◎ (id⟷₁ ⊕ ⟪+⟫ (m +ℕ n) k)))
  ⟷₂⟨ assoc◎r ⟩
    (assocl₊ ◎ (((assocr₊ ◎ (id⟷₁ ⊕ ⟪+⟫ m n)) ⊕ id⟷₁) ◎ (assocr₊ ◎ (id⟷₁ ⊕ ⟪+⟫ (m +ℕ n) k))))
  ⟷₂∎

combNormalForm : {t₁ t₂ : U} → (c : t₁ ⟷₁ t₂) →
  Σ (canonU t₁ ⟷₁ canonU t₂) (λ nc → (!⟷₁ (normC t₁) ◎ c ◎ (normC t₂) ⟷₂ nc))
combNormalForm id⟷₁ = id⟷₁ ,
  trans⟷₂ (id⟷₂ ⊡ idl◎l) rinv◎l
combNormalForm unite₊l = id⟷₁ ,
  trans⟷₂ (uniti₊l⟷₂l ⊡ id⟷₂)
  (trans⟷₂ assoc◎r
  (trans⟷₂ (id⟷₂ ⊡ assoc◎l)
  (trans⟷₂ (id⟷₂ ⊡ (linv◎l ⊡ id⟷₂))
  (trans⟷₂ (id⟷₂ ⊡ idl◎l)
  rinv◎l))))
combNormalForm uniti₊l = id⟷₁ ,
  trans⟷₂ (id⟷₂ ⊡ assoc◎l)
  (trans⟷₂ (id⟷₂ ⊡ (uniti₊l⟷₂l ⊡ id⟷₂))
  (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
  (trans⟷₂ (id⟷₂ ⊡ (id⟷₂ ⊡ linv◎l))
  (trans⟷₂ (id⟷₂ ⊡ idr◎l)
  rinv◎l))))
combNormalForm {t₁ + t₂} {t₂ + t₁} swap₊ = swap-big t₁ t₂ ,
  {!!}
combNormalForm {t₁ + (t₂ + t₃)} assocl₊ = id⟷₁ ,
  {!!}
{--
 ! <+> |t1| |t2+t3| ;
 id + (! (<+> |t2| |t3|)) ;
 ! norm t1 + (! norm t2 + ! norm t3) ;
  assocl+ ;
 (norm t1 + norm t2) + norm t3 ;
 (<+> |t1| |t2|) + id ;
 <+> |t1+t2| |t3|
--}

-- formally:
--   transport (λ X → canonU (t₁ + (t₂ + t₃)) ⟷₁ X)
--             (canonU-assoc t₁ t₂ t₃) id⟷₁ ,
--   {!!}
combNormalForm {(t₁ + t₂) + t₃} assocr₊ = id⟷₁ ,
  {!!}
combNormalForm (c₁ ◎ c₂) with combNormalForm c₁ | combNormalForm c₂
... | nc₁ , eq₁ | nc₂ , eq₂ = (nc₁ ◎ nc₂) ,
  {!!}
combNormalForm (c₁ ⊕ c₂) with combNormalForm c₁ | combNormalForm c₂
... | nc₁ , eq₁ | nc₂ , eq₂ = {!!} ,
  {!!}

--}

{--
     assocrNormalForm : {t₁ t₂ t₃ nt : U} {c : t₁ + (t₂ + t₃) ⟷₁ nt} →
                        (nf : normalForm (t₁ + (t₂ + t₃)) nt c) →
                    combNormalForm assocr₊ (sum+NF nf) nf id⟷₁
                      rinv◎l
     swap0NormalForm : {t nt : U} {c : t ⟷₁ nt} {nf : normalForm t nt c}
                       {nc : nt ⟷₁ nt}
                       {c=nc : (!⟷₁ (unite₊l ◎ c) ◎ swap₊ ◎ swap₊ ◎ unite₊l ◎ c) ⟷₂ nc} →
                    combNormalForm swap₊ (sum0NF nf) (swap0NF (sum0NF nf)) id⟷₁
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎l)
                      (trans⟷₂ (id⟷₂ ⊡ (rinv◎l ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ idl◎l)
                      rinv◎l)))
     swap10NormalForm :
       combNormalForm swap₊ (sum1NF zeroNF) (sum0NF oneNF) id⟷₁
         {!!}
     swap11NormalForm :
       combNormalForm swap₊ (sum1NF oneNF) (sum1NF oneNF) (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
         {!!}
     -- swap1+NormalForm :
     --
     -- I + (a + b)     --------      (a + b) + I
     --                               a + (b + I)
     -- I + a* + b* + 0            a* + b* + I + 0
     --
     -- swap+NormalForm : (t₁ + t₂) + t₃
     {--
       swap₊
       O + t
       I + t
       (t₁ + t₂) + t₃
       {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
       (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
       (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set
     --}
     seqNormalForm : {t₁ t₂ t₃ nt₁ nt₂ nt₃ : U}
                     {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} {c₃ : t₃ ⟷₁ nt₃} →
                     {c₁₂ : t₁ ⟷₁ t₂} {c₂₃ : t₂ ⟷₁ t₃}
                     {nf₁ : normalForm t₁ nt₁ c₁} {nf₂ : normalForm t₂ nt₂ c₂}
                     {nf₃ : normalForm t₃ nt₃ c₃}
                     {nc₁₂ : nt₁ ⟷₁ nt₂} {nc₂₃ : nt₂ ⟷₁ nt₃}
                     {c₁₂=nc₁₂ : (!⟷₁ c₁ ◎ c₁₂ ◎ c₂) ⟷₂ nc₁₂}
                     {c₂₃=nc₂₃ : (!⟷₁ c₂ ◎ c₂₃ ◎ c₃) ⟷₂ nc₂₃} →
                     combNormalForm c₁₂ nf₁ nf₂ nc₁₂ c₁₂=nc₁₂ →
                     combNormalForm c₂₃ nf₂ nf₃ nc₂₃ c₂₃=nc₂₃ →
                    combNormalForm (c₁₂ ◎ c₂₃) nf₁ nf₃ (nc₁₂ ◎ nc₂₃)
                      (trans⟷₂
                        (id⟷₂ ⊡
                          (((trans⟷₂ idr◎r (id⟷₂ ⊡ linv◎r {c = c₂})) ⊡ id⟷₂) ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ ((assoc◎l ⊡ id⟷₂) ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
                      (trans⟷₂ assoc◎l
                      (c₁₂=nc₁₂ ⊡ c₂₃=nc₂₃))))))
     -- sumNormalForm : (c₁ ⊕ c₂)
     {--
       {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
       (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
       (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set
     --}

--}




-----------------------------------------------------------------------------

{--
data normalForm : (t : U) → (nt : U) → (t ⟷₁ nt) → Set where
  zeroNF : normalForm O O id⟷₁
  oneNF  : normalForm I (I + O) (uniti₊l ◎ swap₊)
  sum0NF  : {t nt : U} {c : t ⟷₁ nt} →
           normalForm t nt c →
           normalForm (O + t) nt (unite₊l ◎ c)
  sum1NF  : {t nt : U} {c : t ⟷₁ nt} →
           normalForm t nt c →
           normalForm (I + t) (I + nt) (id⟷₁ ⊕ c)
  sum+NF  : {t₁ t₂ t₃ nt : U} {c : t₁ + (t₂ + t₃) ⟷₁ nt} →
           normalForm (t₁ + (t₂ + t₃)) nt c →
           normalForm ((t₁ + t₂) + t₃) nt (assocr₊ ◎ c)
  swap0NF : {t nt : U} {c : O + t ⟷₁ nt} →
           normalForm (O + t) nt c →
           normalForm (t + O) nt (swap₊ ◎ c)

{-# TERMINATING #-} -- fix later
normalize : (t : U) → Σ U (λ nt → Σ (t ⟷₁ nt) (λ c → normalForm t nt c))
normalize O = O , _ , zeroNF
normalize I = (I + O) , _ , oneNF
normalize (O + t) with normalize t
... | nt , nc , nf = _ , _ , sum0NF nf
normalize (I + t) with normalize t
... | nt , nc , nf = _ , _ , sum1NF nf
normalize ((t₁ + t₂) + t₃) with normalize (t₁ + (t₂ + t₃))
... | nt , nc , nf = _ , _ , sum+NF nf

-- Example of taking a combinator between regular types and producing one
-- between normal forms along with a proof of 2-equivalence

-- For readability
-- Regular Pi combinator on trees


A1 A2 A3 A4 A5 A6 : U
A1 = I
A2 = I
A3 = I
A4 = I
A5 = I
A6 = I

tree : U
tree = ((A1 + A2) + A3) + ((A4 + A5) + A6)

mirrorTree : U
mirrorTree = (A6 + (A5 + A4)) + (A3 + (A2 + A1))

mirror : tree ⟷₁ mirrorTree
mirror = swap₊ ◎ (swap₊ ⊕ swap₊) ◎ ((id⟷₁ ⊕ swap₊) ⊕ (id⟷₁ ⊕ swap₊))

-- Flattened normal-form types

flatTree : U
flatTree = A1 + (A2 + (A3 + (A4 + (A5 + (A6 + O)))))

flatMirrorTree : U
flatMirrorTree = A6 + (A5 + (A4 + (A3 + (A2 + (A1 + O)))))

-- Going from regular Pi types to the normal form

treeNF : Σ (tree ⟷₁ flatTree) (λ c → normalForm tree flatTree c)
treeNF = _ , sum+NF (sum+NF (sum1NF (sum1NF (sum1NF (sum+NF (sum1NF (sum1NF oneNF)))))))

{--
Evaluating treeNF produces
(assocr₊ ◎
 assocr₊ ◎
 id⟷₁ ⊕
 id⟷₁ ⊕ id⟷₁ ⊕ assocr₊ ◎ id⟷₁ ⊕ id⟷₁ ⊕ (uniti₊l ◎ swap₊))
--}

mirrorTreeNF : Σ (mirrorTree ⟷₁ flatMirrorTree) (λ c → normalForm mirrorTree flatMirrorTree c)
mirrorTreeNF = _ , sum+NF (sum1NF (sum+NF (sum1NF (sum1NF (sum1NF (sum1NF oneNF))))))

{--
Evaluating mirrorTreeNF produces
(assocr₊ ◎
 id⟷₁ ⊕
 assocr₊ ◎ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ (uniti₊l ◎ swap₊))
--}

-- Now we want to define a normal form for combinators and relate 'mirror' to its
-- normal form

-- Pay attention to nc below: allowed normal form combinators:
-- nc ::= id⟷₁
--     | !⟷₁ nc
--     | nc ◎ nc
--

data comb+NormalForm : {t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
                    (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
                    (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set where


data combNormalForm : {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
                    (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
                    (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set where
     idNormalForm : {t nt : U} {c : t ⟷₁ nt} → (nf : normalForm t nt c) →
                    combNormalForm id⟷₁ nf nf id⟷₁
                      (trans⟷₂ (id⟷₂ ⊡ idl◎l) rinv◎l)
     uniteNormalForm : {t nt : U} {c : t ⟷₁ nt} → (nf : normalForm t nt c) →
                    combNormalForm unite₊l (sum0NF nf) nf id⟷₁
                      rinv◎l
     unitiNormalForm : {t nt : U} {c : t ⟷₁ nt} → (nf : normalForm t nt c) →
                    combNormalForm uniti₊l nf (sum0NF nf) id⟷₁
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎l)
                      (trans⟷₂ (id⟷₂ ⊡ (linv◎l ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ idl◎l)
                      rinv◎l)))
     assoclNormalForm : {t₁ t₂ t₃ nt : U} {c : t₁ + (t₂ + t₃) ⟷₁ nt} →
                        (nf : normalForm (t₁ + (t₂ + t₃)) nt c) →
                    combNormalForm assocl₊ nf (sum+NF nf) id⟷₁
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎l)
                      (trans⟷₂ (id⟷₂ ⊡ (linv◎l ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ idl◎l) rinv◎l)))
     assocrNormalForm : {t₁ t₂ t₃ nt : U} {c : t₁ + (t₂ + t₃) ⟷₁ nt} →
                        (nf : normalForm (t₁ + (t₂ + t₃)) nt c) →
                    combNormalForm assocr₊ (sum+NF nf) nf id⟷₁
                      rinv◎l
     swap0NormalForm : {t nt : U} {c : t ⟷₁ nt} {nf : normalForm t nt c}
                       {nc : nt ⟷₁ nt}
                       {c=nc : (!⟷₁ (unite₊l ◎ c) ◎ swap₊ ◎ swap₊ ◎ unite₊l ◎ c) ⟷₂ nc} →
                    combNormalForm swap₊ (sum0NF nf) (swap0NF (sum0NF nf)) id⟷₁
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎l)
                      (trans⟷₂ (id⟷₂ ⊡ (rinv◎l ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ idl◎l)
                      rinv◎l)))
     swap10NormalForm :
       combNormalForm swap₊ (sum1NF zeroNF) (sum0NF oneNF) id⟷₁
         {!!}
     swap11NormalForm :
       combNormalForm swap₊ (sum1NF oneNF) (sum1NF oneNF) (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
         {!!}
     -- swap1+NormalForm :
     --
     -- I + (a + b)     --------      (a + b) + I
     --                               a + (b + I)
     -- I + a* + b* + 0            a* + b* + I + 0
     --
     -- swap+NormalForm : (t₁ + t₂) + t₃
     {--
       swap₊
       O + t
       I + t
       (t₁ + t₂) + t₃
       {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
       (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
       (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set
     --}
     seqNormalForm : {t₁ t₂ t₃ nt₁ nt₂ nt₃ : U}
                     {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} {c₃ : t₃ ⟷₁ nt₃} →
                     {c₁₂ : t₁ ⟷₁ t₂} {c₂₃ : t₂ ⟷₁ t₃}
                     {nf₁ : normalForm t₁ nt₁ c₁} {nf₂ : normalForm t₂ nt₂ c₂}
                     {nf₃ : normalForm t₃ nt₃ c₃}
                     {nc₁₂ : nt₁ ⟷₁ nt₂} {nc₂₃ : nt₂ ⟷₁ nt₃}
                     {c₁₂=nc₁₂ : (!⟷₁ c₁ ◎ c₁₂ ◎ c₂) ⟷₂ nc₁₂}
                     {c₂₃=nc₂₃ : (!⟷₁ c₂ ◎ c₂₃ ◎ c₃) ⟷₂ nc₂₃} →
                     combNormalForm c₁₂ nf₁ nf₂ nc₁₂ c₁₂=nc₁₂ →
                     combNormalForm c₂₃ nf₂ nf₃ nc₂₃ c₂₃=nc₂₃ →
                    combNormalForm (c₁₂ ◎ c₂₃) nf₁ nf₃ (nc₁₂ ◎ nc₂₃)
                      (trans⟷₂
                        (id⟷₂ ⊡
                          (((trans⟷₂ idr◎r (id⟷₂ ⊡ linv◎r {c = c₂})) ⊡ id⟷₂) ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ ((assoc◎l ⊡ id⟷₂) ⊡ id⟷₂))
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
                      (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
                      (trans⟷₂ assoc◎l
                      (c₁₂=nc₁₂ ⊡ c₂₃=nc₂₃))))))
     -- sumNormalForm : (c₁ ⊕ c₂)
     {--
       {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
       (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
       (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set
     --}


mirrorNF : Σ (flatTree ⟷₁ flatMirrorTree) (λ nc →
           Σ (!⟷₁ (fst treeNF) ◎ mirror ◎ fst mirrorTreeNF ⟷₂ nc) (λ α →
           combNormalForm mirror (snd treeNF) (snd mirrorTreeNF) nc α))
mirrorNF = _ , _ ,
  seqNormalForm {!!}
  (seqNormalForm {!!}
  {!!})
--}
