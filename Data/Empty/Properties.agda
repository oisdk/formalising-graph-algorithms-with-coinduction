{-# OPTIONS --safe #-}

module Data.Empty.Properties where

open import Data.Empty
open import HLevels
open import Level

isProp⊥ : isProp ⊥
isProp⊥ ()

isProp¬ : isProp (¬ A)
isProp¬ f g i x = isProp⊥ (f x) (g x) i
