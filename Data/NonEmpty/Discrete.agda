{-# OPTIONS --safe #-}

open import Prelude

module Data.NonEmpty.Discrete (disc : Discrete A) where

open import Data.List.Properties.Discrete disc using (_∈?_) renaming (uniq to uniq′)
open import Data.NonEmpty

uniq : List⁺ A → Bool
uniq = uniq′ ∘ not-empty

-- open import Data.Set.Discrete disc 
open import Data.Set using (𝒦; All-𝒦?)
open import Truth

covers : 𝒦 A → List⁺ A → Bool
covers Dom (x ∷ xs) = does (All-𝒦? {P = λ y → |T| (y ∈? x ∷ xs) } (λ y → T? (y ∈? x ∷ xs)) Dom)
