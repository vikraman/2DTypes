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

canonU-assoc : (t₁ t₂ t₃ : U) → canonU (t₁ + (t₂ + t₃)) == canonU ((t₁ + t₂) + t₃)
canonU-assoc t₁ t₂ t₃ rewrite +-assoc (∣ t₁ ∣) (∣ t₂ ∣) (∣ t₃ ∣) = idp

postulate
  canonU-assoc-rewrite : (t₁ t₂ t₃ : U) →
    ⟪ ∣ t₁ ∣ +ℕ ∣ t₂ + t₃ ∣ ⟫ ↦ ⟪ ∣ t₁ + t₂ ∣ +ℕ ∣ t₃ ∣ ⟫

{-# REWRITE canonU-assoc-rewrite #-}

⟪+⟫ : (m n : ℕ) → ⟪ m ⟫ + ⟪ n ⟫ ⟷₁ ⟪ m +ℕ n ⟫
⟪+⟫ O n = unite₊l
⟪+⟫ (S m) n = assocr₊ ◎ (id⟷₁ ⊕ ⟪+⟫ m n)

normC : (t : U) → t ⟷₁ canonU t
normC O = id⟷₁
normC I  = uniti₊l ◎ swap₊
normC (X + Y) = (normC X ⊕ normC Y) ◎ ⟪+⟫ ∣ X ∣ ∣ Y ∣

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
combNormalForm swap₊ = {!!} ,
  {!!}
combNormalForm {t₁ + (t₂ + t₃)} assocl₊ = id⟷₁ ,
  {!!}

{--
 ! <+> |t1| |t2+t3| ;
 ! (norm t1 + (norm t2 + norm t3 ; <+> |t2| |t3|)) ;
 assocl+ ;
 (norm t1 + norm t2 ; <+> |t1| |t2|) + norm t3 ;
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
