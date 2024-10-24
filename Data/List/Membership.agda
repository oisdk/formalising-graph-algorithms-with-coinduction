{-# OPTIONS --safe #-}

module Data.List.Membership where

open import Prelude

infixr 5 _∈_
_∈_ : A → List A → Type _
x ∈ xs = ∃ i × x ≡ (xs !! i)

here : ∀ {x : A} {xs : List A} → x ∈ x ∷ xs
here = fzero , refl

there : ∀ {x y : A} {xs : List A} → x ∈ xs → x ∈ y ∷ xs
there (i , p) = fsuc i , p

infixr 5 _∉_
_∉_ : A → List A → Type _
x ∉ xs = ¬ (x ∈ xs)

module DecidableMembership (_≟_ : Discrete A) where
  _∈?_ : (x : A) (xs : List A) → Dec (x ∈ xs)
  x ∈? [] = no λ ()
  x ∈? (y ∷ xs) with x ≟ y
  (x ∈? (y ∷ xs)) | yes x≡y = yes (fzero , x≡y)
  (x ∈? (y ∷ xs)) | no  x≢y with x ∈? xs
  (x ∈? (y ∷ xs)) | no  x≢y | yes x∈xs = yes (there x∈xs)
  (x ∈? (y ∷ xs)) | no  x≢y | no  x∉xs = no λ { (fsuc i , p) → x∉xs (i , p) ; (fzero , p) → x≢y p }
