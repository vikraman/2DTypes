{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Level0 where

open import lib.Base
open import lib.PathGroupoid
open import lib.types.Nat renaming (_+_ to _+ℕ_)
open import lib.types.Sigma

open import Pi+.Syntax

-----------------------------------------------------------------------------
-- Canonical representation of sum types as lists I + (I + (I + ... O))

∣_∣ : U → ℕ
∣ O ∣ = 0
∣ I ∣ = 1
∣ t₁ + t₂ ∣ = ∣ t₁ ∣ +ℕ ∣ t₂ ∣

⟪_⟫ : ℕ → U
⟪ O ⟫ = O
⟪ S n ⟫ = I + ⟪ n ⟫

canonU : U → U
canonU t = ⟪ ∣ t ∣ ⟫

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
-- Example

-- postulate A B C D E F : U
A B C D E F : U
A = I
B = I
C = I
D = I
E = I
F = I

tree eert : U
tree = ((A + B) + C) + ((D + E) + F)
eert = (F + (E + D)) + (C + (B + A))

-- canonU tree == A + (B + (C + (D + (E + (F + O)))))
-- canonU eert == F + (E + (D + (C + (B + (A + O)))))

-----------------------------------------------------------------------------
-- Special combinators on normal forms

data _⇔_ : (t₁ t₂ : U) → Set where
  id⇔ : {m : ℕ} → ⟪ m ⟫ ⇔ ⟪ m ⟫
  seq⇔ : {m n k : ℕ} → ⟪ m ⟫ ⇔ ⟪ n ⟫ → ⟪ n ⟫ ⇔ ⟪ k ⟫ → ⟪ m ⟫ ⇔ ⟪ k ⟫
  append⇔ : {m n k p : ℕ} → ⟪ m ⟫ ⇔ ⟪ k ⟫ → ⟪ n ⟫ ⇔ ⟪ p ⟫ →
            ⟪ m +ℕ n ⟫ ⇔ ⟪ k +ℕ p ⟫
  assocl⇔ : {m n k : ℕ} → ⟪ m +ℕ (n +ℕ k) ⟫ ⇔ ⟪ (m +ℕ n)  +ℕ k ⟫
  assocr⇔ : {m n k : ℕ} → ⟪ (m +ℕ n) +ℕ k ⟫ ⇔ ⟪ m +ℕ (n +ℕ k) ⟫
  snocN⇔ : {m : ℕ} → ⟪ 1 +ℕ m ⟫ ⇔ ⟪ m +ℕ 1 ⟫
  unit⇔ : {m : ℕ} → ⟪ m ⟫ ⇔ ⟪ m +ℕ 0 ⟫
  -- moves the first element to the end via a sequence of 'm' swaps
  -- swap 0; swap 1; swap 2; ...; swap (m-1)

-----------------------------------------------------------------------------
-- Convert combinators to normal form

bigSwap⇔ : {m n : ℕ} → ⟪ m +ℕ n ⟫ ⇔ ⟪ n +ℕ m ⟫
bigSwap⇔ {O} {n} = unit⇔
bigSwap⇔ {S m} {n} =
  seq⇔ snocN⇔
  (seq⇔ (assocr⇔ {m} {n} {1})
  (seq⇔ (bigSwap⇔ {m} {n +ℕ 1})
  (assocr⇔ {n} {1} {m})))

combNF : {t₁ t₂ : U} → (c : t₁ ⟷₁ t₂) → (canonU t₁ ⇔ canonU t₂)
combNF unite₊l = id⇔
combNF uniti₊l = id⇔
combNF {t₁ + t₂} swap₊ = bigSwap⇔ {∣ t₁ ∣} {∣ t₂ ∣}
combNF {t₁ + (t₂ + t₃)} assocl₊ = assocl⇔ {∣ t₁ ∣}{∣ t₂ ∣}{∣ t₃ ∣}
combNF {(t₁ + t₂) + t₃} assocr₊ = assocr⇔ {∣ t₁ ∣}{∣ t₂ ∣}{∣ t₃ ∣}
combNF id⟷₁ = id⇔
combNF (c₁ ◎ c₂) = seq⇔ (combNF c₁) (combNF c₂)
combNF (c₁ ⊕ c₂) = append⇔ (combNF c₁) (combNF c₂)

-----------------------------------------------------------------------------
-- Example ctd

mirror : tree ⟷₁ eert
mirror = swap₊ ◎ (swap₊ ⊕ swap₊) ◎ ((id⟷₁ ⊕ swap₊) ⊕ (id⟷₁ ⊕ swap₊))

mirrorNF : canonU tree ⇔ canonU eert
mirrorNF = combNF mirror

{--
Keeping A..F as postulates

seq⇔
  (bigSwap⇔ {∣ A ∣ +ℕ ∣ B ∣ +ℕ ∣ C ∣} {∣ D ∣ +ℕ ∣ E ∣ +ℕ ∣ F ∣})
  (seq⇔
    (append⇔
      (bigSwap⇔ {∣ D ∣ +ℕ ∣ E ∣} {∣ F ∣})
      (bigSwap⇔ {∣ A ∣ +ℕ ∣ B ∣} {∣ C ∣}))
    (append⇔
      (append⇔ id⇔
        (bigSwap⇔ {∣ D ∣} {∣ E ∣}))
      (append⇔ id⇔
        (bigSwap⇔ {∣ A ∣} {∣ B ∣}))))

A..F are all set to I

seq⇔
(seq⇔ snocN⇔
 (seq⇔ assocr⇔
  (seq⇔
   (seq⇔ snocN⇔
    (seq⇔ assocr⇔
     (seq⇔ (seq⇔ snocN⇔ (seq⇔ assocr⇔ (seq⇔ unit⇔ assocr⇔))) assocr⇔)))
   assocr⇔)))
(seq⇔
 (append⇔
  (seq⇔ snocN⇔
   (seq⇔ assocr⇔
    (seq⇔ (seq⇔ snocN⇔ (seq⇔ assocr⇔ (seq⇔ unit⇔ assocr⇔))) assocr⇔)))
  (seq⇔ snocN⇔
   (seq⇔ assocr⇔
    (seq⇔ (seq⇔ snocN⇔ (seq⇔ assocr⇔ (seq⇔ unit⇔ assocr⇔))) assocr⇔))))
 (append⇔
  (append⇔ id⇔ (seq⇔ snocN⇔ (seq⇔ assocr⇔ (seq⇔ unit⇔ assocr⇔))))
  (append⇔ id⇔ (seq⇔ snocN⇔ (seq⇔ assocr⇔ (seq⇔ unit⇔ assocr⇔))))))
--}

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

{--

OLD STUFF. KEEP FOR NOW
∣⟪⟫∣ : (n : ℕ) → ∣ ⟪ n ⟫ ∣ == n
∣⟪⟫∣ O = idp
∣⟪⟫∣ (S n) = ap S (∣⟪⟫∣ n)

canon-n : (m : ℕ) → canonU ⟪ m ⟫ == ⟪ m ⟫
canon-n O = idp
canon-n (S m) = ap (λ X → ⟪ S X ⟫) (∣⟪⟫∣ m)

canon-invol : (t : U) → canonU (canonU t) == canonU t
canon-invol t = ap ⟪_⟫ (∣⟪⟫∣ ∣ t ∣)

canonU-assoc : (t₁ t₂ t₃ : U) →
  canonU (t₁ + (t₂ + t₃)) == canonU ((t₁ + t₂) + t₃)
canonU-assoc t₁ t₂ t₃ rewrite +-assoc (∣ t₁ ∣) (∣ t₂ ∣) (∣ t₃ ∣) = idp

-----------------------------------------------------------------------------
-- Define special combinators for canonical forms
-- Want these to be sequences of assocs and swaps

snoc : (m : ℕ) → ⟪ 1 +ℕ m ⟫ ⟷₁ ⟪ m +ℕ 1 ⟫
snoc O = id⟷₁
snoc (S n) = swap01 ◎ (id⟷₁ ⊕ snoc n)

dneppa : (m n : ℕ) → ⟪ m +ℕ n ⟫ ⟷₁ ⟪ n +ℕ m ⟫
dneppa O n = {!!}
dneppa (S m) n =
  ⟪ S (m +ℕ n) ⟫
  ⟷₁⟨ snoc (m +ℕ n) ⟩
  ⟪ (m +ℕ n) +ℕ 1 ⟫
  ⟷₁⟨ {!!} ⟩
  ⟪ m +ℕ (n +ℕ 1) ⟫
  ⟷₁⟨ dneppa m (n +ℕ 1) ⟩
  ⟪ (n +ℕ 1) +ℕ m ⟫
  ⟷₁⟨ {!!} ⟩
  ⟪ n +ℕ S m ⟫ ⟷₁∎

combNormalForm : {t₁ t₂ : U} → (c : t₁ ⟷₁ t₂) →
  Σ (canonU t₁ ⟷₁ canonU t₂) (λ cnf → (!⟷₁ (normC t₁) ◎ c ◎ normC t₂) ⟷₂ cnf)
combNormalForm {t} id⟷₁ = id⟷₁ ,
  trans⟷₂ (id⟷₂ ⊡ idl◎l) rinv◎l
combNormalForm {O + t} unite₊l = id⟷₁ ,
  trans⟷₂ (uniti₊l⟷₂l ⊡ id⟷₂)
  (trans⟷₂ assoc◎r
  (trans⟷₂ (id⟷₂ ⊡ assoc◎l)
  (trans⟷₂ (id⟷₂ ⊡ (linv◎l ⊡ id⟷₂))
  (trans⟷₂ (id⟷₂ ⊡ idl◎l)
  rinv◎l))))
combNormalForm {t} uniti₊l = id⟷₁ ,
  trans⟷₂ (id⟷₂ ⊡ assoc◎l)
  (trans⟷₂ (id⟷₂ ⊡ (uniti₊l⟷₂l ⊡ id⟷₂))
  (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
  (trans⟷₂ (id⟷₂ ⊡ (id⟷₂ ⊡ linv◎l))
  (trans⟷₂ (id⟷₂ ⊡ idr◎l)
  rinv◎l))))
combNormalForm {t₁ + t₂} swap₊ = dneppa ∣ t₁ ∣ ∣ t₂ ∣ ,
  {!!}
combNormalForm {t₁ + (t₂ + t₃)} assocl₊ = {!!} ,
  {!!}
combNormalForm {(t₁ + t₂) + t₃} assocr₊ = {!!} ,
  {!!}
combNormalForm (_◎_ {t₁} {t₂} {t₃} c₁ c₂) =
  let (c1nf , p1) = combNormalForm c₁
      (c2nf , p2) = combNormalForm c₂
  in (c1nf ◎ c2nf) ,
     (trans⟷₂
     (id⟷₂ ⊡ (((trans⟷₂ idr◎r (id⟷₂ ⊡ linv◎r {c = c₂})) ⊡ id⟷₂) ⊡ id⟷₂))
     (trans⟷₂ (id⟷₂ ⊡ ((assoc◎l ⊡ id⟷₂) ⊡ id⟷₂))
     (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
     (trans⟷₂ (id⟷₂ ⊡ assoc◎r)
     (trans⟷₂ assoc◎l
     {!!})))))
combNormalForm {t₁ + t₂} {t₃ + t₄} (c₁ ⊕ c₂) =
  let (c1nf , p1) = combNormalForm c₁
      (c2nf , p2) = combNormalForm c₂
  in (!⟷₁ ⟪++⟫ ◎ (c1nf ⊕ c2nf) ◎ ⟪++⟫) ,
  {!!}
combNormalForm swap01 = {!!} ,
  {!!}

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
mirrorNF = fst (combNormalForm mirror)

-----------------------------------------------------------------------------

infix 100 _″

_″ : ∀ {t₁ t₂} → t₁ ⇔ t₂ → t₁ ⟷₁ t₂
(id⇔ eq) ″ = idupto⟷₁ {_} {_} {ap canonU eq}
seq⇔ c₁ c₂ ″ = c₁ ″ ◎ c₂ ″
bigplus⇔ c₁ c₂ ″ = !⟷₁ ⟪++⟫ ◎ (c₁ ″ ⊕ c₂ ″) ◎ ⟪++⟫
bigswap⇔ {t₁} {t₂} ″ = dneppa ∣ t₁ ∣ ∣ t₂ ∣

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
