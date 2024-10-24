{-# OPTIONS --safe #-}

module Data.NonEmpty where

open import Prelude

infixr 5 _∷_
record List⁺ (A : Type a) : Type a where
  constructor _∷_; eta-equality
  field
    head : A
    tail : List A

open List⁺ public

not-empty : List⁺ A → List A
not-empty (x ∷ xs) = x ∷ xs
