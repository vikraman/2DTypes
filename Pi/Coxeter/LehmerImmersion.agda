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
open import Pi.Extra
open import Pi.Misc

open import Pi.Lehmer.Lehmer public

immersion : {n : ℕ} -> Lehmer n -> Listℕ
immersion {0} CanZ = nil
immersion {S n} (CanS l {r} r≤1+n) = (immersion l) ++ (((S n) ∸ r) ↓ r)

immersion->> : {n : ℕ} -> (cl : Lehmer n) -> n >> immersion cl
immersion->> {.0} CanZ = nil
immersion->> {S n} (CanS {n} cl {r} rn) =
  let p = immersion->> {n} cl
  in  >>-++ (>>-S p) (>>-↓ (S n) (S n ∸ r) r (≤-reflexive (plus-minus rn)))

canonical-lift : {n : ℕ} -> (m : ℕ) -> (n ≤ m) -> (cln : Lehmer n) -> Σ (Lehmer m) (λ clm -> immersion {m} clm == immersion {n} cln)
canonical-lift {n} m p cln with ≤-∃ _ _ p
canonical-lift {.m} m p cln | 0 , idp = cln , idp
canonical-lift {n} .(S (fst + n)) p cln | S fst , idp =
  let rec-m , rec-p = canonical-lift {n} (fst + n) (≤-up-+ rrr) cln
  in  (CanS rec-m z≤n) , (≡-trans ++-unit rec-p)

>>-drop : {n : ℕ} -> (cl : Lehmer n) -> (m : ℕ) -> (m >> (immersion cl)) -> Σ (Lehmer m) (λ cln -> immersion cln == immersion cl)
>>-drop {O} CanZ m nil =  canonical-lift m z≤n CanZ
>>-drop {S n} (CanS cl {O} x) m mcl =
  let rec-l , rec-p = >>-drop {n} cl m (transport (λ e → m >> e) ++-unit mcl)
  in  rec-l , (rec-p ∙ ! ++-unit)
>>-drop {S n} (CanS cl {S r} x) O mcl = ⊥-elim (1+n≰n (≤-trans (>>-implies-> mcl idp) z≤n))
>>-drop {S n} (CanS cl {S r} x) (S m) mcl =
  let n<m = >>-implies-> mcl idp
  in  canonical-lift (S m) (≤-trans (≤-up2 (≤-reflexive (! (plus-minus (≤-down2 x))))) n<m) (CanS cl {S r} x)

-- l0 : Lehmer 0
-- l0 = CanZ
-- l1 : Lehmer 1
-- l1 = CanS {0} CanZ {1} (s≤s z≤n)
-- l2 : Lehmer 2
-- l2 = CanS l1 {2} (s≤s (s≤s z≤n))

-- ll2 : Listℕ
-- ll2 = immersion {2} l2
