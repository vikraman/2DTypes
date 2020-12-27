{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Level0 where

open import lib.Base
open import lib.types.Nat renaming (_+_ to _+ℕ_)

open import Pi+.Syntax as Pi

ℕ→Pi : ℕ → U
ℕ→Pi O = O
ℕ→Pi (S x) = I + (ℕ→Pi x)

⟪_⟫ : ℕ → U
⟪ O ⟫ = O
⟪ S n ⟫ = I + ⟪ n ⟫

∣_∣ : U → ℕ
∣ O ∣ = 0
∣ I ∣ = 1
∣ X + Y ∣ = ∣ X ∣ +ℕ ∣ Y ∣

∣⟪_⟫∣ : (n : ℕ) → ∣ ⟪ n ⟫ ∣ == n
∣⟪ O ⟫∣ = idp
∣⟪ S n ⟫∣ = ap S ∣⟪ n ⟫∣

canonU : U → U
canonU T = ⟪ ∣ T ∣ ⟫

⟪+⟫ : (m n : ℕ) → ⟪ m ⟫ + ⟪ n ⟫ ⟷₁ ⟪ m +ℕ n ⟫
⟪+⟫ O n = unite₊l
⟪+⟫ (S m) n = assocr₊ ◎ (id⟷₁ ⊕ ⟪+⟫ m n)

normC : (t : U) → t ⟷₁ canonU t
normC O = id⟷₁
normC I  = uniti₊l ◎ swap₊
normC (X + Y) = (normC X ⊕ normC Y) ◎ ⟪+⟫ ∣ X ∣ ∣ Y ∣

-- Experiment
-- Mirror tree; flatten

-- Flat list of types

data UList : Set where
  Zer : UList
  Suc : ⊤ → UList → UList

append : UList → UList → UList
append Zer us = us
append (Suc t ts) us = Suc t (append ts us)

flatten : U → UList
flatten O = Zer
flatten I = Suc unit Zer
flatten (t₁ + t₂) = append (flatten t₁) (flatten t₂)

-- Regular Pi types are trees; combinators are tree isos

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

-- Flatten the tree and derive the isos on the list representation

flatTree : UList
flatTree = flatten tree
         -- Suc A1 (Suc A2 (Suc A3 (Suc A4 (Suc A5 (Suc A6 Zer)))))

flatMirrorTree : UList
flatMirrorTree = flatten mirrorTree
         -- Suc A6 (Suc A5 (Suc A4 (Suc A3 (Suc A2 (Suc A1 Zer)))))

postulate
  append-assoc : (A B C : U) →
    append (flatten A) (append (flatten B) (flatten C)) ==
    append (append (flatten A) (flatten B)) (flatten C)

data _⇔_ : (ts us : UList) → Set where
  idList : {ts : UList} → ts ⇔ ts
  swapList : {ts us vs : UList} → (j k : ℕ) →
             (append ts (Suc unit (append us (Suc unit vs)))) ⇔
             (append ts (Suc unit (append us (Suc unit vs))))
             -- swaps the two units at positions j and k; length ts = j-1 etc.
  symList : {ts us : UList} → (ts ⇔ us) → (us ⇔ ts)
  seqList : {ts us vs : UList} → (ts ⇔ us) → (us ⇔ vs) → (ts ⇔ vs)
  appendList : {ts us vs ws : UList} → (ts ⇔ us) → (vs ⇔ ws) →
               (append ts vs) ⇔ (append us ws)

flattenComb : {A B : U} → (c : A ⟷₁ B) → (flatten A ⇔ flatten B)
flattenComb unite₊l = idList
flattenComb {t₁ + t₂} {t₂ + t₁} swap₊ =
  appendList (swapList 0 3)
  (appendList (swapList 1 4) (swapList 2 5))
  -- assuming (flatten t₁) has length 3
flattenComb {t₁ + (t₂ + t₃)} {(t₁ + t₂) + t₃} assocl₊ rewrite append-assoc t₁ t₂ t₃ = idList
flattenComb id⟷₁ = idList
flattenComb (!⟷₁ c) = symList (flattenComb c)
flattenComb (c₁ ◎ c₂) = seqList (flattenComb c₁) (flattenComb c₂)
flattenComb (c₁ ⊕ c₂) = appendList
                          (flattenComb c₁) -- say of length k
                          (flattenComb c₂) -- after adding k to every index

flatMirror : flatTree ⇔ flatMirrorTree
flatMirror = flattenComb mirror
