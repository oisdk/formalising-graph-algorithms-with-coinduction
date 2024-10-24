{-# OPTIONS --safe #-}

module Data.List.Syntax where

open import Prelude hiding ([_])

VecT : ℕ → Type a → Type a
VecT zero    A = A
VecT (suc n) A = A × VecT n A

[_] : ∀ {n} → VecT n A → List A
[_] {n = zero}  x = x ∷ []
[_] {n = suc n} (x , xs) = x ∷ [ xs ]

