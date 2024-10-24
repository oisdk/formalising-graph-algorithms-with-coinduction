{-# OPTIONS --without-K --safe #-}

module Data.Sum.Definition where

open import Level

infixr 3 _⊎_
data _⊎_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
