{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module PiFin+.ListPerm where

open import HoTT

module _ {i} {C : Type i} where

  remove : {x : C} (xs : List C) → x ∈ xs → List C
  remove nil ()
  remove (x :: xs) (here idp) = xs
  remove (x :: xs) (there p) = remove xs p

  data ListPerm : List C → List C → Type i where
    lpnil : ListPerm nil nil
    lpcons : {x : C} {xs xs' : List C}
           → (e : x ∈ xs')
           → ListPerm xs (remove xs' e)
           → ListPerm (x :: xs) xs'

  ListPerm-nil-l : {xs : List C} → ListPerm nil xs → xs == nil
  ListPerm-nil-l lpnil = idp

  ListPerm-nil-r : {xs : List C} → ListPerm xs nil → xs == nil
  ListPerm-nil-r lpnil = idp
  ListPerm-nil-r (lpcons () p)

  ∈-:: : {x y : C} {xs : List C} → y ∈ xs → y ∈ (x :: xs)
  ∈-:: (here idp) = there (here idp)
  ∈-:: (there e) = there (∈-:: e)

  ∈-ListPerm : x ∈ xs → ListPerm xs ys → x ∈ ys
  ∈-ListPerm

  first-here : {y : C} {xs ys : List C} → ListPerm xs (y :: ys) → y ∈ xs
  first-here {y} {xs} {ys} p = {!!}

  -- first-here : {x y : C} {xs ys : List C} → ListPerm (x :: xs) (y :: ys) → y ∈ (x :: xs)
  -- first-here {.y} {y} {xs} {ys} (lpcons (here idp) p) = here idp
  -- first-here {x} {y} {xs} {nil} (lpcons (there ()) p)
  -- first-here {x} {y} {xs} {y' :: ys} (lpcons (there e) p) = {!!}

  remove-first-here : {y : C} {xs ys : List C} → ListPerm xs {!!} → ListPerm {!!} {!!}
  remove-first-here = {!!}

  ListPerm-is-refl : is-refl ListPerm
  ListPerm-is-refl nil = lpnil
  ListPerm-is-refl (x :: xs) = lpcons (here idp) (ListPerm-is-refl xs)

  ListPerm-is-sym : is-sym ListPerm
  ListPerm-is-sym lpnil = lpnil
  ListPerm-is-sym (lpcons (here idp) p) = lpcons (here idp) (ListPerm-is-sym p)
  ListPerm-is-sym q@(lpcons (there e) p) = lpcons {!!} {!!} -- lpcons (first-here q) (ListPerm-is-sym (remove-first-here q))

  ListPerm-is-trans : is-trans ListPerm
  ListPerm-is-trans lpnil lpnil = lpnil
  ListPerm-is-trans (lpcons () p) lpnil
  ListPerm-is-trans (lpcons (here idp) p) (lpcons e q) = lpcons e (ListPerm-is-trans p q)
  ListPerm-is-trans (lpcons (there e) p) (lpcons f q) = {!!}
