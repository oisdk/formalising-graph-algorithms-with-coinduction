{-# OPTIONS --safe #-}

module Data.Empty where

open import Level
open import Cubical.Data.Empty using (⊥) public

infixr 5 ¬_
¬_ : Type a → Type a
¬ A = A → ⊥

absurd : ⊥ → A
absurd ()

map-¬ : (A → B) → ¬ B → ¬ A
map-¬ f ¬y x = ¬y (f x)
