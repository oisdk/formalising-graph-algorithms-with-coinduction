{-# OPTIONS --safe #-}

module Data.List.Tabulate where

open import Prelude
open import Data.List
open import Data.Fin

private variable n : ℕ

tabulate : (Fin n → A) → List A
tabulate {n = zero} f = []
tabulate {n = suc n} f = f fzero ∷ tabulate (f ∘ fsuc)

open import Data.List.Membership

tabulate-∈ : (f : Fin n → A) (x : Fin n) → f x ∈ tabulate f
tabulate-∈ {n = suc n} f fzero = here
tabulate-∈ {n = suc n} f (fsuc x) = there (tabulate-∈ (f ∘ fsuc) x)
