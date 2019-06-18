{-# OPTIONS --cubical #-}

module scratch.Pi3 where

open import Cubical.Core.Everything
open import Cubical.Basics.Everything

_∘_ = compPath

data Pi3 : Set where
  b : Pi3
  sh1 : b ≡ b
  sh2 : b ≡ b
  s01 : b ≡ b
  s12 : b ≡ b
  s02 : b ≡ b
  sh12 : sh1 ∘ sh2 ≡ refl
  sh21 : sh2 ∘ sh1 ≡ refl
  s0101 : s01 ∘ s01 ≡ refl
  s1212 : s12 ∘ s12 ≡ refl
  s0202 : s02 ∘ s02 ≡ refl

data Three : Set where
  Zero One Two : Three

shift1 : Three → Three
shift1 Zero = One
shift1 One = Two
shift1 Two = Zero

shift2 : Three → Three
shift2 Zero = Two
shift2 One = Zero
shift2 Two = One

shift1Path : Three ≡ Three
shift1Path = isoToPath shift1 shift2
                       (λ { Zero → refl ; One → refl ; Two → refl })
                       (λ { Zero → refl ; One → refl ; Two → refl })

shift2Path : Three ≡ Three
shift2Path = isoToPath shift2 shift1
                       (λ { Zero → refl ; One → refl ; Two → refl })
                       (λ { Zero → refl ; One → refl ; Two → refl })

shift12Path : shift1Path ∘ shift2Path ≡ refl
shift12Path = {!!}

swap01 : Three → Three
swap01 Zero = One
swap01 One = Zero
swap01 Two = Two

swap01Path : Three ≡ Three
swap01Path = isoToPath swap01 swap01
                       (λ { Zero → refl ; One → refl ; Two → refl })
                       (λ { Zero → refl ; One → refl ; Two → refl })

swap12 : Three → Three
swap12 Zero = Zero
swap12 One = Two
swap12 Two = One

swap12Path : Three ≡ Three
swap12Path = isoToPath swap12 swap12
                       (λ { Zero → refl ; One → refl ; Two → refl })
                       (λ { Zero → refl ; One → refl ; Two → refl })

swap02 : Three → Three
swap02 Zero = Two
swap02 One = One
swap02 Two = Zero

swap02Path : Three ≡ Three
swap02Path = isoToPath swap02 swap02
                       (λ { Zero → refl ; One → refl ; Two → refl })
                       (λ { Zero → refl ; One → refl ; Two → refl })

El : Pi3 → Set
El b = Three
El (sh1 i) = shift1Path i
El (sh2 i) = shift2Path i
El (s01 i) = swap01Path i
El (s12 i) = swap12Path i
El (s02 i) = swap02Path i
El (sh12 i j) = {!!}
El (sh21 i j) = {!!}
El (s0101 i j) = {!!}
El (s1212 i j) = {!!}
El (s0202 i j) = {!!}
