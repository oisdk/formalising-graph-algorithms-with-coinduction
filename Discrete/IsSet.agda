{-# OPTIONS --safe #-}

module Discrete.IsSet where

open import Discrete
open import Decidable
open import Level
open import Path
open import HLevels

Discrete→isSet :
  Discrete A → isSet A
Discrete→isSet d = Stable≡→isSet (λ x y → Dec→Stable (x ≡ y) (d x y))

isPropDiscrete :
  isProp (Discrete A)
isPropDiscrete f g i x y = isPropDec (Discrete→isSet f x y) (f x y) (g x y) i
