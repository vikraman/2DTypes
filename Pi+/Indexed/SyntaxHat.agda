{-# OPTIONS --without-K  --rewriting #-}

module Pi+.Indexed.SyntaxHat where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.types.Sigma
open import lib.PathOver

open import lib.PathGroupoid

open import lib.Equivalence
import lib.types.Nat as N

open import Pi+.Extra
open import Pi+.Misc

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

data _⟷_  : ℕ → ℕ → Type₀ where
  swap₊^   : S (S n) ⟷ S (S n)
  id⟷₁^    : n ⟷ n
  _◎^_     : (n ⟷ m) → (m ⟷ o) → (n ⟷ o)
  ⊕^_      : (n ⟷ m) → (S n ⟷ S m)

siz : {n m : ℕ} -> (n ⟷ m) -> n == m
siz swap₊^ = idp
siz id⟷₁^ = idp
siz (c₁ ◎^ c₂) = siz c₁ ∙ siz c₂
siz (⊕^ c) = ap S (siz c)

i^ : (n : ℕ) -> U^ n
i^ O = O
i^ (S n) = I+ i^ n

data my : (n : ℕ) → Type₀ where
  swap₊^   : my (S (S n))
  id⟷₁^    : my n
  _◎^_     : (my n) → (my n) → (my n)
  ⊕^_      : (my n) → (my (S n))

my2 : (n m : ℕ) → Type₀
my2 n m = (n == m) × my n

ℕ-p : {n : ℕ} -> (p : n == n) -> p == idp
ℕ-p p = (prop-has-all-paths {{has-level-apply N.ℕ-level _ _}} p idp)

module _ where
  f : (my2 n m) → n ⟷ m
  f (idp , swap₊^) = swap₊^
  f (idp , id⟷₁^) = id⟷₁^
  f (idp , (c ◎^ c₂)) = (f (idp , c)) ◎^ (f (idp , c₂))
  f (idp , (⊕^ c)) = ⊕^ (f (idp , c))

  g : (n ⟷ m) → (my2 n m)
  g swap₊^ = idp , swap₊^
  g id⟷₁^ = idp , id⟷₁^
  g (c ◎^ c₁) = 
    let (p1 , r1) = g c
        (p2 , r2) = g c₁
    in  (p1 ∙ p2) , (r1 ◎^ transport my (! p1) r2)
  g (⊕^ c) = 
    let (p , r) = g c
    in  (ap S p) , (⊕^ r)

  f-g : (c : n ⟷ m) → f (g c) == c
  f-g swap₊^ = idp
  f-g id⟷₁^ = idp
  f-g (x ◎^ x₁) with (siz x) with (siz x₁)
  ... | idp | idp rewrite (ℕ-p (fst (g x))) rewrite (ℕ-p (fst (g x₁))) =
    let r1 = f-g x
        r2 = f-g x₁
    in  ap2 _◎^_ (ap f (pair= (! (ℕ-p _)) (↓-cst-in idp)) ∙ r1) (ap f (pair= (! (ℕ-p _)) (↓-cst-in idp)) ∙ r2)
  f-g (⊕^_ {n = n} {m = m} x) with (siz x)
  ... | idp rewrite (ℕ-p (ap S (fst (g x)))) = 
    let r = f-g x
    in  ap ⊕^_ (ap f (pair= (prop-has-all-paths {{has-level-apply N.ℕ-level _ _}} _ _) (↓-cst-in idp)) ∙ r)

  g-f : (c : my2 n m) → g (f c) == c
  g-f (idp , swap₊^) = idp
  g-f (idp , id⟷₁^) = idp
  g-f (idp , (c₁ ◎^ c₂)) rewrite (ap snd (g-f (idp , c₂))) rewrite (ap fst (g-f (idp , c₁))) =
    let r1 = g-f (idp , c₁)
        r2 = g-f (idp , c₂)
    in  pair= (ℕ-p _) (↓-cst-in (ap2 (λ x y → x ◎^ y) (ap snd r1) idp))
  g-f (idp , (⊕^ c)) rewrite (ap fst (g-f (idp , c))) rewrite (ap snd (g-f (idp , c))) = idp

  my-equiv : (my2 n m) ≃ (n ⟷ m)
  my-equiv = equiv f g f-g g-f

U^-is-Singleton : (t₁ t₂ : U^ n) → (t₁ == t₂)
U^-is-Singleton O O = idp
U^-is-Singleton (I+ t₁) (I+ t₂) = ap I+_ (U^-is-Singleton t₁ t₂)

U^-is-singleton=idp : (t : U^ n) → U^-is-Singleton t t == idp
U^-is-singleton=idp O = idp
U^-is-singleton=idp (I+ t) = ap (ap I+_) (U^-is-singleton=idp t)

postulate
    U^-is-singleton=idp-rewrite : {t : U^ n} → (U^-is-Singleton t t) ↦ idp -- U^-is-singleton=idp
    {-# REWRITE U^-is-singleton=idp-rewrite #-}

ff : {n m : ℕ} {t₁ : U^ n} {t₂ : U^ m} → (t₁ ⟷₁^ t₂) -> (n ⟷ m)
ff swap₊^ = swap₊^
ff id⟷₁^ = id⟷₁^
ff (x ◎^ x₁) = (ff x) ◎^ (ff x₁)
ff (⊕^ x) = ⊕^ ff x

gg : {n m : ℕ} → (n ⟷ m) → {t₁ : U^ n} {t₂ : U^ m} -> (t₁ ⟷₁^ t₂)
gg {n = .(S (S _))} {m = .(S (S _))} swap₊^ {t₁ = I+ I+ t₁} {t₂ = I+ I+ t₂} = transport (λ x → I+ (I+ t₁) ⟷₁^ I+ (I+ x)) (U^-is-Singleton t₁ t₂) swap₊^
gg {n = n} {m = .n} id⟷₁^ {t₁ = t₁} {t₂ = t₂} = transport (λ x → (t₁ ⟷₁^ x)) (U^-is-Singleton t₁ t₂) id⟷₁^
gg {n = n} {m = m} (_◎^_ {n₁} {m₁} {o₁} x x₁) {t₁ = t₁} {t₂ = t₂} = 
  let r1 = gg {n} {_} x {t₁} {i^ m₁} 
      r2 = gg {_} {m} x₁ {i^ m₁} {t₂}
  in  r1 ◎^ r2
gg {n = .(S _)} {m = .(S _)} (⊕^ c) {t₁ = I+ t₁} {t₂ = I+ t₂} = 
  let r = gg c
  in  ⊕^ r

ff-gg : {n m : ℕ} {t₁ : U^ n} {t₂ : U^ m} → (c : n ⟷ m) -> ff {n} {m} {t₁} {t₂} (gg c) == c
ff-gg {.(S (S _))} {.(S (S _))} {I+ I+ t₁} {I+ I+ t₂} swap₊^ rewrite (U^-is-Singleton t₁ t₂) = idp
ff-gg {t₁ = t₁} {t₂ = t₂} id⟷₁^ rewrite (U^-is-Singleton t₁ t₂) = idp
ff-gg (x ◎^ x₁) = (ap2 (λ c d -> c ◎^ d) (ff-gg x) (ff-gg x₁))
ff-gg {t₁ = I+ t₁} {t₂ = I+ t₂} (⊕^ x) = ap ⊕^_ (ff-gg x)
gg-ff : {n m : ℕ} {t₁ : U^ n} {t₂ : U^ m} → (c : t₁ ⟷₁^ t₂) -> gg (ff c) == c
gg-ff (swap₊^ {t = t}) = idp
gg-ff (id⟷₁^ {t = t}) = idp
gg-ff {n = n₁} {m = m₁} (_◎^_ {n} {m} {o} {t₂ = t₃} x  x₁) rewrite (U^-is-Singleton (i^ o) t₃) = idp ∙ (ap2 (λ c d -> c ◎^ d) (gg-ff x) (gg-ff x₁))
gg-ff (⊕^ x) = ap ⊕^_  (gg-ff x)

⟷-equiv : {n m : ℕ} {t₁ : U^ n} {t₂ : U^ m} → (t₁ ⟷₁^ t₂) ≃ (n ⟷ m)
⟷-equiv = equiv ff (λ x → gg x) ff-gg gg-ff

⟷₁-equiv :  {n m : ℕ} {t₁ : U^ n} {t₂ : U^ m} → (t₁ ⟷₁^ t₂) ≃ (my2 n m)
⟷₁-equiv = my-equiv ⁻¹ ∘e ⟷-equiv  

induction^^ :
        (P : {n : ℕ} {t : U^ n} → (t ⟷₁^ t) → Type₀)
    → (swap* : {n : ℕ} {t : U^ n} → P (swap₊^ {t = t}))
    → (id* : {n : ℕ} {t : U^ n} → P (id⟷₁^ {t = t}))
    → (comp* : {n : ℕ}  {t : U^ n} {c₁ : t ⟷₁^ t} {c₂ : t ⟷₁^ t} → P c₁ → P c₂ → P (c₁ ◎^ c₂))
    → (plus* : {n : ℕ} {t : U^ n} {c : t ⟷₁^ t} → P (⊕^_ c))
    → {n : ℕ} → {t : U^ n} → (c : my2 n n) → P {n = n} {t = t} (<– ⟷₁-equiv c)
induction^^ P swap* id* comp* plus* {t = I+ (I+ t)} (pp , swap₊^) rewrite (ℕ-p pp) = swap*
induction^^ P swap* id* comp* plus* {t = t} (pp , id⟷₁^) rewrite (ℕ-p pp) = id*
induction^^ P swap* id* comp* plus* {n = n} {t = t} (pp , (c₁ ◎^ c₂)) rewrite (ℕ-p pp) rewrite (U^-is-Singleton (i^ n) t) = 
  let r1 = induction^^ P swap* id* comp* plus* {n = n} {t = t} (idp , c₁)
      r2 = induction^^ P swap* id* comp* plus* {n = n} {t = t} (idp , c₂)
  in  comp* r1 r2
induction^^ P swap* id* comp* plus* {t = I+ t} (pp , (⊕^ c)) rewrite (ℕ-p pp) = plus* {t = t} {c = <– ⟷₁-equiv (idp , c)}

induction :
      (P : {n : ℕ} {t : U^ n} → (t ⟷₁^ t) → Type₀)
    → (swap* : {n : ℕ} {t : U^ n} → P (swap₊^ {t = t}))
    → (id* : {n : ℕ} {t : U^ n} → P (id⟷₁^ {t = t}))
    → (comp* : {n : ℕ} {t : U^ n} {c₁ : t ⟷₁^ t} {c₂ : t ⟷₁^ t} → P c₁ → P c₂ → P (c₁ ◎^ c₂))
    → (plus* : {n : ℕ} {t : U^ n} {c : t ⟷₁^ t} → P (⊕^_ c))
    → {t : U^ n} → (c : t ⟷₁^ t) → P c
induction P swap* id* comp* plus* c =
  let r = induction^^ P swap* id* comp* plus* (–> ⟷₁-equiv c)
      s = transport (λ e -> P (gg e)) (f-g (ff c)) r
      q = transport (λ e -> P e) (gg-ff c) s
  in  q

!⟷₁^ : t₁ ⟷₁^ t₂ → t₂ ⟷₁^ t₁
!⟷₁^ swap₊^ = swap₊^
!⟷₁^ id⟷₁^ = id⟷₁^
!⟷₁^ (c₁ ◎^ c₂) = !⟷₁^ c₂ ◎^ !⟷₁^ c₁
!⟷₁^ (⊕^ c₁) = ⊕^ (!⟷₁^ c₁)


⟷₁^-eq-size : {n m : ℕ} {t₁ : U^ n} {t₂ : U^ m} -> (t₁ ⟷₁^ t₂) -> n == m
⟷₁^-eq-size swap₊^ = idp
⟷₁^-eq-size id⟷₁^ = idp
⟷₁^-eq-size (c₁ ◎^ c₂) = ⟷₁^-eq-size c₁ ∙ ⟷₁^-eq-size c₂
⟷₁^-eq-size (⊕^ c) = ap S (⟷₁^-eq-size c)

⊥-⟷₁ : (t : U^ n) → ((I+ t₁) ⟷₁^ O) → ⊥
⊥-⟷₁ _ c = N.S≰O _ (inl (⟷₁^-eq-size c))

down-id₊^ : {t₁ : U^ m} {t₂ : U^ n} → (I+ t₁ ⟷₁^ I+ t₂) → t₁ ⟷₁^ t₂
down-id₊^ swap₊^ = id⟷₁^
down-id₊^ id⟷₁^ = id⟷₁^
down-id₊^ (_◎^_ {t₁ = t₁} {t₂ = O} c c₁) = ⊥-elim  (⊥-⟷₁ t₁ c)
down-id₊^ (_◎^_ {t₂ = I+ t₂} c c₁) = down-id₊^ c ◎^ down-id₊^ c₁
down-id₊^ (⊕^ c) = c

-- big-id₊^ : {t₁ : U^ m} {t₂ : U^ n} → (t₁ ⟷₁^ t₂) → t₁ ⟷₁^ t₂

lemma : {t₁ : U^ m} {t₂ : U^ n} → (p : m == n) → t₁ == t₂ [ U^ ↓ p ]
lemma idp = U^-is-Singleton _ _

lemma' : {t₁ : U^ m} {t₂ : U^ n} → (p : m == n) → (t₁ == t₂ [ U^ ↓ p ]) -> t₁ ⟷₁^ t₂
lemma' idp q = transport (λ x → _ ⟷₁^ x) q id⟷₁^

big-id₊^ : {t₁ : U^ m} {t₂ : U^ n} → (t₁ ⟷₁^ t₂) → t₁ ⟷₁^ t₂
big-id₊^ {m = m} {n = n} {t₁} {t₂} c = 
  let pn : m == n
      pn = ⟷₁^-eq-size c
      p : t₁ == t₂ [ U^ ↓ pn ]
      p = lemma pn
  in lemma' pn p

big-swap₊^ : {t₁ : U^ m} {t₂ : U^ n} → (t₁ ⟷₁^ t₂) → I+ (I+ t₁) ⟷₁^ I+ (I+ t₂)
big-swap₊^ swap₊^ = swap₊^
big-swap₊^ id⟷₁^ = swap₊^
big-swap₊^ (c₁ ◎^ c₂) = (big-swap₊^ c₁) ◎^ big-id₊^ (⊕^ (⊕^ c₂))
big-swap₊^ (⊕^ c) = swap₊^ ◎^ big-id₊^ ((⊕^ (⊕^ (⊕^ c))))


-- 2-combinators

data _⟷₂^_ : {X : U^ n} {Y : U^ m} → X ⟷₁^ Y → X ⟷₁^ Y → Set where
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

big-id₊^-ap : {t₁ : U^ m} {t₂ : U^ n} → {c₁ c₂ : t₁ ⟷₁^ t₂} → (α : c₁ ⟷₂^ c₂) → big-id₊^ c₁ ⟷₂^ big-id₊^ c₂
big-id₊^-ap α = TODO

c₊⟷₂id⟷₁ : (c : O ⟷₁^ O) → c ⟷₂^ id⟷₁^
c₊⟷₂id⟷₁ id⟷₁^ = id⟷₂^
c₊⟷₂id⟷₁ (_◎^_ {t₂ = O} c₁ c₂) = trans⟷₂^ (c₊⟷₂id⟷₁ c₁ ⊡^ c₊⟷₂id⟷₁ c₂) idl◎l^
c₊⟷₂id⟷₁ (_◎^_ {t₂ = I+ t₂} c₁ c₂) with (⟷₁^-eq-size c₂)
... | ()

lemma'' : {t : U^ n} → (c : t ⟷₁^ t) → (⟷₁^-eq-size c) == idp
lemma'' c = prop-has-all-paths ⦃ has-level-apply N.ℕ-level _ _ ⦄ _ _

lemma3 : {A B : Type₀} {x y : A} (P : B → Type₀) (f : A → B) (p : x == y) (u : P (f x)) → transport P (ap f p) u == transport (P ∘ f) p u
lemma3 P f idp u = idp

big-id₊⟷₂id⟷₁ : {t : U^ n} → (c : t ⟷₁^ t) → big-id₊^ c ⟷₂^ id⟷₁^
big-id₊⟷₂id⟷₁ {t = t} c rewrite (lemma'' c) = id⟷₂^

-- -- -- 3-combinators trivial

data _⟷₃^_ : {X Y : U^ n} {p q : X ⟷₁^ Y} → (p ⟷₂^ q) → (p ⟷₂^ q) → Set where
  trunc : {X Y : U^ n} {p q : X ⟷₁^ Y} (α β : p ⟷₂^ q) → α ⟷₃^ β
