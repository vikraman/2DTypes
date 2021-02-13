{-# OPTIONS --without-K --exact-split --rewriting --allow-unsolved-metas #-}

module Pi+.Indexed.SyntaxNorm where

open import lib.Base
open import lib.NType
open import lib.PathOver
import lib.types.Nat as N

open import Pi+.Extra

private
    variable
      m n o p q r : ℕ

-- Types

data U^ : ℕ → Type₀ where
  O : U^ 0
  I+_ : U^ n → U^ (S n)

private
    variable
      t t₁ t₂ t₃ t₄ t₅ t₆ : U^ n

infixr 40 I+_
infix 30 _⟷₁^_
infixr 50 _◎^_ ⊕^_

-- 1-combinators

data _⟷₁^_  : U^ m → U^ n → Type₀ where
  swap₊^   : I+ (I+ t) ⟷₁^ I+ (I+ t)
  id⟷₁^    : t ⟷₁^ t
  _◎^_     : (t₁ ⟷₁^ t₂) → (t₂ ⟷₁^ t₃) → (t₁ ⟷₁^ t₃)
  ⊕^_      : (t₁ ⟷₁^ t₂) → (I+ t₁ ⟷₁^ I+ t₂)

-- down₊^ : {t₁ : U^ m} {t₂ : U^ n} → (I+ t₁ ⟷₁^ I+ t₂) → t₁ ⟷₁^ t₂
-- down₊^ {t₁ = O} {t₂ = O} c = id⟷₁^
-- down₊^ {t₁ = O} {t₂ = I+ t₂} c = {!   !}
-- down₊^ {t₁ = I+ t₁} {t₂ = O} c = {!   !}
-- down₊^ {t₁ = I+ t₁} {t₂ = I+ t₂} c = {!   !}

-- big-id₊^ : {t₁ : U^ m} {t₂ : U^ n} → (t₁ ⟷₁^ t₂) → t₁ ⟷₁^ t₂
-- big-id₊^ swap₊^ = id⟷₁^
-- big-id₊^ id⟷₁^ = id⟷₁^
-- big-id₊^ (c₁ ◎^ c₂) = big-id₊^ c₁ ◎^ big-id₊^  c₂
-- big-id₊^ (⊕^ c) = ⊕^ (big-id₊^ c)

!⟷₁^ : t₁ ⟷₁^ t₂ → t₂ ⟷₁^ t₁
!⟷₁^ swap₊^ = swap₊^
!⟷₁^ id⟷₁^ = id⟷₁^
!⟷₁^ (c₁ ◎^ c₂) = !⟷₁^ c₂ ◎^ !⟷₁^ c₁
!⟷₁^ (⊕^ c₁) = ⊕^ (!⟷₁^ c₁)


⟷₁-eq-size : {n m : ℕ} {t₁ : U^ n} {t₂ : U^ m} -> (t₁ ⟷₁^ t₂) -> n == m
⟷₁-eq-size swap₊^ = idp
⟷₁-eq-size id⟷₁^ = idp
⟷₁-eq-size (c₁ ◎^ c₂) = ⟷₁-eq-size c₁ ∙ ⟷₁-eq-size c₂
⟷₁-eq-size (⊕^ c) = ap S (⟷₁-eq-size c)

⊥-⟷₁ : (t : U^ n) → ((I+ t₁) ⟷₁^ O) → ⊥
⊥-⟷₁ _ c = N.S≰O _ (inl (⟷₁-eq-size c))

down-id₊^ : {t₁ : U^ m} {t₂ : U^ n} → (I+ t₁ ⟷₁^ I+ t₂) → t₁ ⟷₁^ t₂
down-id₊^ swap₊^ = id⟷₁^
down-id₊^ id⟷₁^ = id⟷₁^
down-id₊^ (_◎^_ {t₁ = t₁} {t₂ = O} c c₁) = ⊥-elim  (⊥-⟷₁ t₁ c)
down-id₊^ (_◎^_ {t₂ = I+ t₂} c c₁) = down-id₊^ c ◎^ down-id₊^ c₁
down-id₊^ (⊕^ c) = c

-- big-id₊^ : {t₁ : U^ m} {t₂ : U^ n} → (t₁ ⟷₁^ t₂) → t₁ ⟷₁^ t₂

big-id₊^ : {t₁ : U^ m} {t₂ : U^ n} → (t₁ ⟷₁^ t₂) → t₁ ⟷₁^ t₂
big-id₊^ {m = O} {n = O} {O} {O} c = id⟷₁^
big-id₊^ {m = O} {n = S n} {O} {I+ t₂} c = ⊥-elim (⊥-⟷₁ t₂ (!⟷₁^ c))
big-id₊^ {m = S m} {n = O} {I+ t₁} {t₂ = O} c = ⊥-elim (⊥-⟷₁ t₁ c)
big-id₊^ {m = S m} {n = S n} {I+ t₁} {I+ t₂} c = ⊕^ (big-id₊^ (down-id₊^ c))

-- lemma : (t₁ : U^ m) (t₂ : U^ n) → (p : m == n) → t₁ == t₂ [ U^ ↓ p ]
-- lemma t₁ t₂ p = ?

-- -- U^ n = Σ ℕ (λ m → m == n)

-- big-id₊^ : {t₁ : U^ m} {t₂ : U^ n} → (t₁ ⟷₁^ t₂) → t₁ ⟷₁^ t₂
-- big-id₊^ {t₁ = t₁} c =
--   let p : m == n
--       p = ?
--       q : t₁ == t₂ [ U^ ↓ p ]
--       q = lemma _ _ p
--   in transport (λ t → t₁ ⟷₁^ t) (to-transp q) id⟷₁^

big-swap₊^ : {t₁ : U^ m} {t₂ : U^ n} → (t₁ ⟷₁^ t₂) → I+ (I+ t₁) ⟷₁^ I+ (I+ t₂)
big-swap₊^ swap₊^ = swap₊^
big-swap₊^ id⟷₁^ = swap₊^
big-swap₊^ (c₁ ◎^ c₂) = (big-swap₊^ c₁) ◎^ big-id₊^ (⊕^ (⊕^ c₂))
big-swap₊^ (⊕^ c) = swap₊^ ◎^ big-id₊^ ((⊕^ (⊕^ (⊕^ c))))


-- 2-combinators

data _⟷₂^_ : {X : U^ m} {Y : U^ n} → X ⟷₁^ Y → X ⟷₁^ Y → Set where
  assoc◎l^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₂ ⟷₁^ t₃} {c₃ : t₃ ⟷₁^ t₄} →
          (c₁ ◎^ (c₂ ◎^ c₃)) ⟷₂^ ((c₁ ◎^ c₂) ◎^ c₃)
  assoc◎r^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₂ ⟷₁^ t₃} {c₃ : t₃ ⟷₁^ t₄} →
          ((c₁ ◎^ c₂) ◎^ c₃) ⟷₂^ (c₁ ◎^ (c₂ ◎^ c₃))
  -- assocl₊l^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₃ ⟷₁^ t₄} {c₃ : t₅ ⟷₁^ t₆} →
  --         ((c₁ ⊕ (c₂ ⊕ c₃)) ◎^ assocl₊) ⟷₂^ (assocl₊ ◎^ ((c₁ ⊕ c₂) ⊕ c₃))
  -- assocl₊r^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₃ ⟷₁^ t₄} {c₃ : t₅ ⟷₁^ t₆} →
  --         (assocl₊ ◎^ ((c₁ ⊕ c₂) ⊕ c₃)) ⟷₂^ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎^ assocl₊)
  -- assocr₊r^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₃ ⟷₁^ t₄} {c₃ : t₅ ⟷₁^ t₆} →
  --         (((c₁ ⊕ c₂) ⊕ c₃) ◎^ assocr₊) ⟷₂^ (assocr₊ ◎^ (c₁ ⊕ (c₂ ⊕ c₃)))
  -- assocr₊l^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₃ ⟷₁^ t₄} {c₃ : t₅ ⟷₁^ t₆} →
  --          (assocr₊ ◎^ (c₁ ⊕ (c₂ ⊕ c₃))) ⟷₂^ (((c₁ ⊕ c₂) ⊕ c₃) ◎^ assocr₊)
  idl◎l^   : {c : t₁ ⟷₁^ t₂} → (id⟷₁^ ◎^ c) ⟷₂^ c
  idl◎r^   : {c : t₁ ⟷₁^ t₂} → c ⟷₂^ id⟷₁^ ◎^ c
  idr◎l^   : {c : t₁ ⟷₁^ t₂} → (c ◎^ id⟷₁^) ⟷₂^ c
  idr◎r^   : {c : t₁ ⟷₁^ t₂} → c ⟷₂^ (c ◎^ id⟷₁^)
  linv◎l^  : {c : t₁ ⟷₁^ t₂} → (c ◎^ !⟷₁^ c) ⟷₂^ id⟷₁^
  linv◎r^  : {c : t₁ ⟷₁^ t₂} → id⟷₁^ ⟷₂^ (c ◎^ !⟷₁^ c)
  rinv◎l^  : {c : t₁ ⟷₁^ t₂} → (!⟷₁^ c ◎^ c) ⟷₂^ id⟷₁^
  rinv◎r^  : {c : t₁ ⟷₁^ t₂} → id⟷₁^ ⟷₂^ (!⟷₁^ c ◎^ c)
  -- unite₊l⟷₂l^ : {c₁ : O ⟷₁^ O} {c₂ : t₁ ⟷₁^ t₂} →
  --         (unite₊l ◎^ c₂) ⟷₂^ ((c₁ ⊕ c₂) ◎^ unite₊l)
  -- unite₊l⟷₂r^ : {c₁ : O ⟷₁^ O} {c₂ : t₁ ⟷₁^ t₂} →
  --         ((c₁ ⊕ c₂) ◎^ unite₊l) ⟷₂^ (unite₊l ◎^ c₂)
  -- uniti₊l⟷₂l^ : {c₁ : O ⟷₁^ O} {c₂ : t₁ ⟷₁^ t₂} →
  --         (uniti₊l ◎^ (c₁ ⊕ c₂)) ⟷₂^ (c₂ ◎^ uniti₊l)
  -- uniti₊l⟷₂r^ : {c₁ : O ⟷₁^ O} {c₂ : t₁ ⟷₁^ t₂} →
  --         (c₂ ◎^ uniti₊l) ⟷₂^ (uniti₊l ◎^ (c₁ ⊕ c₂))
  -- swapl₊⟷₂^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₃ ⟷₁^ t₄} →
  --         (swap₊ ◎^ (c₁ ⊕ c₂)) ⟷₂^ ((c₂ ⊕ c₁) ◎^ swap₊)
  -- swapr₊⟷₂^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₃ ⟷₁^ t₄} →
  --         ((c₂ ⊕ c₁) ◎^ swap₊) ⟷₂^ (swap₊ ◎^ (c₁ ⊕ c₂))
  id⟷₂^     : {c : t₁ ⟷₁^ t₂} → c ⟷₂^ c
  trans⟷₂^ : {c₁ c₂ c₃ : t₁ ⟷₁^ t₂} →
         (c₁ ⟷₂^ c₂) → (c₂ ⟷₂^ c₃) → (c₁ ⟷₂^ c₃)
  _⊡^_ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₂ ⟷₁^ t₃} {c₃ : t₁ ⟷₁^ t₂} {c₄ : t₂ ⟷₁^ t₃} →
         (c₁ ⟷₂^ c₃) → (c₂ ⟷₂^ c₄) → (c₁ ◎^ c₂) ⟷₂^ (c₃ ◎^ c₄)
  -- split⊕-id⟷₁^ : (id⟷₁^ {t = t₁ + t₂}) ⟷₂^ (id⟷₁^ ⊕ id⟷₁)

  -- associativity triangle
  -- triangle₊l :
  --   (unite₊r {t = t₁} ⊕ id⟷₁^ {t = t₂}) ⟷₂^ assocr₊ ◎^ (id⟷₁^ ⊕ unite₊l)
  -- triangle₊r :
  --   assocr₊ ◎^ (id⟷₁^ {t = t₁} ⊕ unite₊l {t = t₂}) ⟷₂^ unite₊r ⊕ id⟷₁
  -- pentagon₊l :
  --   assocr₊ ◎^ (assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃ + t₄}) ⟷₂
  --   ((assocr₊ ⊕ id⟷₁) ◎^ assocr₊) ◎^ (id⟷₁^ ⊕ assocr₊)
  -- pentagon₊r :
  --   ((assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃} ⊕ id⟷₁^ {t = t₄}) ◎^ assocr₊) ◎^ (id⟷₁^ ⊕ assocr₊) ⟷₂
  --   assocr₊ ◎^ assocr₊
--   -- unit coherence
  -- unite₊l-coh-l : unite₊l {t = t₁} ⟷₂^ swap₊ ◎^ unite₊r
  -- unite₊l-coh-r : swap₊ ◎^ unite₊r ⟷₂^ unite₊l {t = t₁}
  -- hexagonr₊l :
  --   (assocr₊ ◎^ swap₊) ◎^ assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃} ⟷₂
  --   ((swap₊ ⊕ id⟷₁) ◎^ assocr₊) ◎^ (id⟷₁^ ⊕ swap₊)
  -- hexagonr₊r :
  --   ((swap₊ ⊕ id⟷₁) ◎^ assocr₊) ◎^ (id⟷₁^ ⊕ swap₊) ⟷₂
  --   (assocr₊ ◎^ swap₊) ◎^ assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}
  -- hexagonl₊l :
  --   (assocl₊ ◎^ swap₊) ◎^ assocl₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃} ⟷₂
  --   ((id⟷₁^ ⊕ swap₊) ◎^ assocl₊) ◎^ (swap₊ ⊕ id⟷₁)
  -- hexagonl₊r :
  --   ((id⟷₁^ ⊕ swap₊) ◎^ assocl₊) ◎^ (swap₊ ⊕ id⟷₁) ⟷₂
  --   (assocl₊ ◎^ swap₊) ◎^ assocl₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}
  -- Braiding compatible with unitors (redundant; provable from above
  -- axioms. See for example Thm. 10 in "On MacLane's Conditions for
  -- Coherence of Natural Associativities, Commutativities, etc.
  -- Kelly 1964)
  -- unit-braid : unite₊l {O} ⟷₂^ swap₊ ◎^ unite₊l
  -- braid-unit : swap₊ ◎^ unite₊l ⟷₂^ unite₊l {O}
  
  -- New ones
  ⊕id⟷₁⟷₂^ : ⊕^ id⟷₁^ {t = t₂} ⟷₂^ id⟷₁^
  !⊕id⟷₁⟷₂^ : id⟷₁^ ⟷₂^ ⊕^ id⟷₁^ {t = t₂}
  hom◎⊕⟷₂^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₂ ⟷₁^ t₃} → 
         ((⊕^ c₁) ◎^ (⊕^ c₂)) ⟷₂^ ⊕^ (c₁ ◎^ c₂)
  resp⊕⟷₂  :
         {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₁ ⟷₁^ t₂} → (c₁ ⟷₂^ c₂) → (⊕^ c₁) ⟷₂^ (⊕^ c₂)
  hom⊕◎⟷₂^ : {c₁ : t₁ ⟷₁^ t₂} {c₂ : t₂ ⟷₁^ t₃} → 
         ⊕^ (c₁ ◎^ c₂) ⟷₂^ ((⊕^ c₁) ◎^ (⊕^ c₂))

  swapr₊⟷₂^ : {t : U^ n} {c : t ⟷₁^ t} 
    → (⊕^ (⊕^ c)) ◎^ swap₊^ ⟷₂^ swap₊^ ◎^ (⊕^ (⊕^ c))
  swapl₊⟷₂^ : {t : U^ n} {c : t ⟷₁^ t} 
    → swap₊^ ◎^ (⊕^ (⊕^ c)) ⟷₂^ (⊕^ (⊕^ c)) ◎^ swap₊^

-- -- -- Equational reasoning

infixr 10 _⟷₂^⟨_⟩_
infix  15 _⟷₂^∎

_⟷₂^⟨_⟩_ : ∀ (c₁ : t₁ ⟷₁^ t₂) {c₂ c₃ : t₁ ⟷₁^ t₂} →
         (c₁ ⟷₂^ c₂) → (c₂ ⟷₂^ c₃) → (c₁ ⟷₂^ c₃)
_ ⟷₂^⟨ β ⟩ γ = trans⟷₂^ β γ

_⟷₂^∎ : ∀ (c : t₁ ⟷₁^ t₂) → c ⟷₂^ c
_ ⟷₂^∎ = id⟷₂^

!⟷₂^ : {c₁ c₂ : t₁ ⟷₁^ t₂} → (α : c₁ ⟷₂^ c₂) → (c₂ ⟷₂^ c₁)
!⟷₂^ assoc◎l^ = assoc◎r^
!⟷₂^ assoc◎r^ = assoc◎l^
!⟷₂^ idl◎l^ = idl◎r^
!⟷₂^ idl◎r^ = idl◎l^
!⟷₂^ idr◎l^ = idr◎r^
!⟷₂^ idr◎r^ = idr◎l^
!⟷₂^ linv◎l^ = linv◎r^
!⟷₂^ linv◎r^ = linv◎l^
!⟷₂^ rinv◎l^ = rinv◎r^
!⟷₂^ rinv◎r^ = rinv◎l^
!⟷₂^ id⟷₂^ = id⟷₂^
!⟷₂^ (trans⟷₂^ α α₁) = trans⟷₂^ (!⟷₂^ α₁) (!⟷₂^ α)
!⟷₂^ (α ⊡^ α₁) = !⟷₂^ α ⊡^ !⟷₂^ α₁
!⟷₂^ ⊕id⟷₁⟷₂^ = !⊕id⟷₁⟷₂^
!⟷₂^ !⊕id⟷₁⟷₂^ = ⊕id⟷₁⟷₂^
!⟷₂^ hom◎⊕⟷₂^ = hom⊕◎⟷₂^
!⟷₂^ (resp⊕⟷₂ α) = resp⊕⟷₂ (!⟷₂^ α)
!⟷₂^ hom⊕◎⟷₂^ = hom◎⊕⟷₂^
!⟷₂^ swapl₊⟷₂^ = swapr₊⟷₂^
!⟷₂^ swapr₊⟷₂^ = swapl₊⟷₂^

idf^ : {n : ℕ} {t₁ t₂ : U^ n} → t₁ ⟷₁^ t₂
idf^ {t₁ = O} {t₂ = O} = id⟷₁^
idf^ {t₁ = I+ t₁} {t₂ = I+ t₂} = ⊕^ idf^

i^ : (n : ℕ) -> U^ n
i^ O = O
i^ (S n) = I+ i^ n

big-id₊^-ap : {t₁ : U^ m} {t₂ : U^ n} → {c₁ c₂ : t₁ ⟷₁^ t₂} → (α : c₁ ⟷₂^ c₂) → big-id₊^ c₁ ⟷₂^ big-id₊^ c₂
big-id₊^-ap α = TODO

-- -- -- 3-combinators trivial

data _⟷₃_ : {X Y : U^ n} {p q : X ⟷₁^ Y} → (p ⟷₂^ q) → (p ⟷₂^ q) → Set where
  trunc : {X Y : U^ n} {p q : X ⟷₁^ Y} (α β : p ⟷₂^ q) → α ⟷₃ β

-- -- --
