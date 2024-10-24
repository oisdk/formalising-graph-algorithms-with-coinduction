{-# OPTIONS --safe #-}

module Data.Lift.Properties where

open import Prelude

isSetLift : isSet A → isSet (Lift {ℓ₂ = b} A)
isSetLift isSetA (lift x) (lift y) p q = cong (cong lift) (isSetA x y (cong lower p) (cong lower q))
