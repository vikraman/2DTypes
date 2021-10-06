{-# OPTIONS --without-K --rewriting #-}

module Pi.Coxeter.LehmerImmersion where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.NType
open import lib.PathGroupoid

open import Pi.Common.Arithmetic
open import Pi.Common.ListN
open import Pi.Common.LList
open import Pi.Common.Extra
open import Pi.Common.Misc

open import Pi.Lehmer.Lehmer public

-- This corresponds to the em function in the paper
immersion : {n : ℕ} -> Lehmer n -> Listℕ
immersion {0} CanZ = nil
immersion {S n} (CanS l {r} r≤1+n) = (immersion l) ++ (((S n) ∸ r) ↓ r)

-- But instead of using (l : List (Fin n)), we use (n >> l) type for easier manipulation of the elements of the list
immersion->> : {n : ℕ} -> (cl : Lehmer n) -> n >> immersion cl
immersion->> {.0} CanZ = nil
immersion->> {S n} (CanS {n} cl {r} rn) =
  let p = immersion->> {n} cl
  in  >>-++ (>>-S p) (>>-↓ (S n) (S n ∸ r) r (≤-reflexive (plus-minus rn)))

-- It is possible to "lift" a Lehmer code by appending zeros to it
canonical-lift : {n : ℕ} -> (m : ℕ) -> (n ≤ m) -> (cln : Lehmer n) -> Σ (Lehmer m) (λ clm -> immersion {m} clm == immersion {n} cln)
canonical-lift {n} m p cln with ≤-∃ _ _ p
canonical-lift {.m} m p cln | 0 , idp = cln , idp
canonical-lift {n} .(S (fst + n)) p cln | S fst , idp =
  let rec-m , rec-p = canonical-lift {n} (fst + n) (≤-up-+ rrr) cln
  in  (CanS rec-m z≤n) , (≡-trans ++-unit rec-p)

-- And correspondingly, to reverse this operation
>>-drop : {n : ℕ} -> (cl : Lehmer n) -> (m : ℕ) -> (m >> (immersion cl)) -> Σ (Lehmer m) (λ cln -> immersion cln == immersion cl)
>>-drop {O} CanZ m nil =  canonical-lift m z≤n CanZ
>>-drop {S n} (CanS cl {O} x) m mcl =
  let rec-l , rec-p = >>-drop {n} cl m (transport (λ e → m >> e) ++-unit mcl)
  in  rec-l , (rec-p ∙ ! ++-unit)
>>-drop {S n} (CanS cl {S r} x) O mcl = ⊥-elim (1+n≰n (≤-trans (>>-implies-> mcl idp) z≤n))
>>-drop {S n} (CanS cl {S r} x) (S m) mcl =
  let n<m = >>-implies-> mcl idp
  in  canonical-lift (S m) (≤-trans (≤-up2 (≤-reflexive (! (plus-minus (≤-down2 x))))) n<m) (CanS cl {S r} x)
