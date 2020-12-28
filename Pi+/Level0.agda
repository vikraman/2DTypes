{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Level0 where

open import lib.Base
open import lib.types.Nat renaming (_+_ to _+ℕ_)
open import lib.types.Sigma

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

-- Flat list of types; as subset of Pi types

data normalForm : (t : U) → (nt : U) → (t ⟷₁ nt) → Set where
  zeroNF : normalForm O O id⟷₁
  oneNF  : normalForm I (I + O) (!⟷₁ (swap₊ ◎ unite₊l))
  sum0NF  : {t nt : U} {c : t ⟷₁ nt} →
           normalForm t nt c →
           normalForm (O + t) nt (unite₊l ◎ c)
  sum1NF  : {t nt : U} {c : t ⟷₁ nt} →
           normalForm t nt c →
           normalForm (I + t) (I + nt) (id⟷₁ ⊕ c)
  sum+NF  : {t₁ t₂ t₃ nt : U} {c : t₁ + (t₂ + t₃) ⟷₁ nt} →
           normalForm (t₁ + (t₂ + t₃)) nt c →
           normalForm ((t₁ + t₂) + t₃) nt (!⟷₁ assocl₊ ◎ c)

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

A1 A2 A3 A4 A5 A6 : U
A1 = I
A2 = I
A3 = I
A4 = I
A5 = I
A6 = I

-- Regular Pi combinator on trees

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
(!⟷₁ assocl₊ ◎
 !⟷₁ assocl₊ ◎
 id⟷₁ ⊕
 id⟷₁ ⊕ id⟷₁ ⊕ !⟷₁ assocl₊ ◎ id⟷₁ ⊕ id⟷₁ ⊕ !⟷₁ (swap₊ ◎ unite₊l))
--}

mirrorTreeNF : Σ (mirrorTree ⟷₁ flatMirrorTree) (λ c → normalForm mirrorTree flatMirrorTree c)
mirrorTreeNF = _ , sum+NF (sum1NF (sum+NF (sum1NF (sum1NF (sum1NF (sum1NF oneNF))))))

{--
Evaluating mirrorTreeNF produces
(!⟷₁ assocl₊ ◎
 id⟷₁ ⊕
 !⟷₁ assocl₊ ◎ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ !⟷₁ (swap₊ ◎ unite₊l))
--}

-- Now we want to define a normal form for combinators and relate 'mirror' to its
-- normal form

postulate -- either prove or add to constructors in Syntax
  !₂ : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷₁ t₂} → (α : c₁ ⟷₂ c₂) → (!⟷₁ c₁ ⟷₂ !⟷₁ c₂)
  !!₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₂ ⟷₁ t₁} {c : t₂ ⟷₁ t₃} {c₂ : t₃ ⟷₁ t₄} →
        (nc : t₁ ⟷₁ t₄) → (!⟷₁ c₂ ◎ !⟷₁ c ◎ c₁) ⟷₂ (!⟷₁ (!⟷₁ c₁ ◎ c ◎ c₂))

data combNormalForm : {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
                      (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
                      (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set where
     idNormalForm : {t nt : U} {c : t ⟷₁ nt} → (nf : normalForm t nt c) →
                    combNormalForm id⟷₁ nf nf id⟷₁ (trans⟷₂ (id⟷₂ ⊡ idl◎l) rinv◎l)
     uniteNormalForm : {t nt : U} {c : t ⟷₁ nt} → (nf : normalForm t nt c) →
                    combNormalForm unite₊l (sum0NF nf) nf id⟷₁ rinv◎l
     assoclNormalForm : {t₁ t₂ t₃ nt : U} {c : t₁ + (t₂ + t₃) ⟷₁ nt} →
                        (nf : normalForm (t₁ + (t₂ + t₃)) nt c) →
                        combNormalForm assocl₊ nf (sum+NF nf) id⟷₁
                          (trans⟷₂ (id⟷₂ ⊡ assoc◎l)
                          (trans⟷₂ (id⟷₂ ⊡ (linv◎l ⊡ id⟷₂))
                          (trans⟷₂ (id⟷₂ ⊡ idl◎l) rinv◎l)))
     invNormalForm : {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂}
                     {c : t₁ ⟷₁ t₂} {nf₁ : normalForm t₁ nt₁ c₁} {nf₂ : normalForm t₂ nt₂ c₂}
                     {nc : nt₁ ⟷₁ nt₂} {c=nc : (!⟷₁ c₁ ◎ c ◎ c₂) ⟷₂ nc} →
                     combNormalForm c nf₁ nf₂ nc c=nc →
                     combNormalForm (!⟷₁ c) nf₂ nf₁ (!⟷₁ nc)
                       (trans⟷₂ (!!₂ nc)  (!₂ c=nc))
     -- swapNormalForm : swap₊
     {--
       {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
       (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
       (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set
     --}
     -- seqNormalForm : (c₁ ◎ c₂)
     {--
       {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
       (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
       (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set
     --}
     -- sumNormalForm : (c₁ ⊕ c₂)
     {--
       {t₁ t₂ nt₁ nt₂ : U} {c₁ : t₁ ⟷₁ nt₁} {c₂ : t₂ ⟷₁ nt₂} →
       (c : t₁ ⟷₁ t₂) → normalForm t₁ nt₁ c₁ → normalForm t₂ nt₂ c₂ →
       (nc : nt₁ ⟷₁ nt₂) → (!⟷₁ c₁ ◎ c ◎ c₂ ⟷₂ nc) → Set
     --}

mirrorNF : combNormalForm
  mirror
  (sum+NF (sum+NF (sum1NF (sum1NF (sum1NF (sum+NF (sum1NF (sum1NF oneNF))))))))
  (sum+NF (sum1NF (sum+NF (sum1NF (sum1NF (sum1NF (sum1NF oneNF)))))))
  {!!}
  {!!}
mirrorNF = {!!}
