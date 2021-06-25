{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

module Pi+.Coxeter.InvTransform where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.types.List
open import lib.types.Nat

open import Pi+.Common.FinHelpers
open import Pi+.UFin.BAut
open import Pi+.Misc
open import Pi+.Extra

inv : {n : ℕ} → Fin n → Fin n
inv {S n} (O , _) = n , ltS
inv {S n} (S k , f) = ⟨ inv {n} (k , <-cancel-S f) ⟩

⟨⟩-S⟨⟩ : {n : ℕ} → (k : Fin n) → ⟨ S⟨ k ⟩ ⟩ == S⟨ ⟨ k ⟩ ⟩
⟨⟩-S⟨⟩ {n} k = fin= idp

inv-⟨⟩ : (n : ℕ) → (k : Fin n) → inv {S n} ⟨ k ⟩ == S⟨ inv {n} k ⟩
inv-⟨⟩ (S n) (O , p) = idp
inv-⟨⟩ (S n) (S k , p) =
   let r = inv-⟨⟩ (n) (k , <-cancel-S p)
       t : (k , <-trans ltS p) ==
           ⟨ k , <-cancel-S p ⟩
       t = fin= idp
       s : ⟨ inv {S n} (k , <-trans ltS p) ⟩ ==
           ⟨ inv {S n} ⟨ k , <-cancel-S p ⟩ ⟩
       s = ap (⟨_⟩ ∘ inv {S n}) t
   in  s ∙ (ap ⟨_⟩ r) ∙ (⟨⟩-S⟨⟩ _)

inv-inv : {n : ℕ} → (k : Fin n) → inv (inv k) == k
inv-inv {S O} (O , ϕ) =
  fin= idp
inv-inv {S (S n)} (O , ϕ) =
  fin= (ap fst (inv-inv {S n} (O , O<S n)))
inv-inv {S n} (S k , ϕ) = 
    let r = ap fst (inv-inv {n} (k , <-cancel-S ϕ))
        p  = snd (inv (k , <-cancel-S ϕ))
    in  inv-⟨⟩ n (_ , p) ∙ fin= (ap S r)


-- inv0 : (inv {6} (0 , ltSR (ltSR (ltSR (ltSR (ltSR ltS)))) )) .fst == 5
-- inv0 = idp
-- inv1 : (inv {6} (1 , ltSR (ltSR (ltSR (ltSR ltS))) )) .fst == 4
-- inv1 = idp
-- inv2 : (inv {6} (2 , ltSR (ltSR (ltSR ltS)) )) .fst == 3
-- inv2 = idp
-- inv3 : (inv {6} (3 , ltSR (ltSR ltS) )) .fst == 2
-- inv3 = idp
-- inv4 : (inv {6} (4 , ltSR ltS )) .fst == 1
-- inv4 = idp
-- inv5 : (inv {6} (5 , ltS )) .fst == 0
-- inv5 = idp

-- inv-equiv : {n : ℕ} → Aut (Fin n)
-- inv-equiv {O} = ide _
-- inv-equiv {S n} = equiv inv inv inv-inv inv-inv

-- -- given permutuation p
-- -- k → n - p(n - k)

-- npnk-> : {n : ℕ} → (p : Aut (Fin n)) → Fin n → Fin n
-- npnk-> p = (λ k → inv (–> p (inv k) ))

-- <-npnk : {n : ℕ} → (p : Aut (Fin n)) → Fin n → Fin n
-- <-npnk p = (λ k → inv (<– p (inv k) ))

-- abstract
--   npnk-self-inv-l : {n : ℕ} → (p : Aut (Fin n)) → (k : Fin n) → <-npnk p (npnk-> p k) == k
--   npnk-self-inv-l {n} p k =
--       let q = ap (inv ∘ (<– p)) (inv-inv (–> p (inv k)))
--           r = <–-inv-l p (inv k)
--       in  q ∙ ap inv r ∙ inv-inv k

--   npnk-self-inv-r : {n : ℕ} → (p : Aut (Fin n)) → (k : Fin n) → npnk-> p (<-npnk p k) == k
--   npnk-self-inv-r {n} p k =
--       let q = ap (inv ∘ (–> p)) (inv-inv (<– p (inv k)))
--           r = <–-inv-r p (inv k)
--       in  q ∙ ap inv r ∙ inv-inv k

-- inv-transform : {n : ℕ} → Aut (Fin n) → Aut (Fin n)
-- inv-transform p = equiv (npnk-> p) (<-npnk p) (npnk-self-inv-r p) (npnk-self-inv-l p)

-- inv-transform-equiv : {n : ℕ} → Aut (Fin n) ≃ Aut (Fin n)
-- inv-transform-equiv = equiv inv-transform inv-transform
--             (λ b → e= (λ y → inv-inv _ ∙ ap (–> b) (inv-inv y)))
--             (λ b → e= (λ y → inv-inv _ ∙ ap (–> b) (inv-inv y)))
