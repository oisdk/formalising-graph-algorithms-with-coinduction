{-# OPTIONS --safe #-}

open import Prelude

module Data.List.Properties.Discrete {a} {A : Type a} (disc : Discrete A) where

open import Data.List.Properties

private
  infix 4 _≟_
  _≟_ : Discrete A
  _≟_ = disc

infixr 5 _∈?_
_∈?_ : A → List A → Bool
_∈?_ x = foldr (λ y ys → does (x ≟ y) || ys) false

uniq : List A → Bool
uniq [] = true
uniq (x ∷ xs) = neg (x ∈? xs) && uniq xs
