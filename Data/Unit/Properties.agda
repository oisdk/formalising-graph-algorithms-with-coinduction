{-# OPTIONS --safe #-}

module Data.Unit.Properties where

open import Data.Unit
open import HLevels
open import Path

isProp⊤ : isProp ⊤
isProp⊤ _ _ = refl
