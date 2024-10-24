{-# OPTIONS --safe #-}

open import Algebra
open import Level

module Data.Weighted {ℓ} {𝑆 : Type ℓ} (sgp : Semigroup 𝑆) where

open import Data.Weighted.Definition sgp public
open import Data.Weighted.Eliminators sgp public
open import Data.Weighted.Condition sgp public
open import Data.Weighted.CommutativeMonoid sgp public
