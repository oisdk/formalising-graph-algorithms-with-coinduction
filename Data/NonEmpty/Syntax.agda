{-# OPTIONS --safe #-}

module Data.NonEmpty.Syntax where

open import Prelude hiding ([_])
open import Data.NonEmpty
import Data.List.Syntax as List

VecT : ℕ → Type a → Type a
VecT zero    A = A
VecT (suc n) A = A × List.VecT n A

[_] : ∀ {n} → VecT n A → List⁺ A
[_] {n = zero}  x = x ∷ []
[_] {n = suc n} (x , xs) = x ∷ List.[ xs ]
