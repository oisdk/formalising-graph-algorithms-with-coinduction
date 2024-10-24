{-# OPTIONS --safe #-}

module Data.List where

open import Agda.Builtin.List
  using (List; []; _∷_)
  public

open import Level

private
  variable
    y : A
    xs : List A


foldr : (A → B → B) → B → List A → B
foldr f b []       = b
foldr f b (x ∷ xs) = f x (foldr f b xs)

para : (A → List A → B → B) → B → List A → B
para f b [] = b
para f b (x ∷ xs) = f x xs (para f b xs)

foldl : (B → A → B) → B → List A → B
foldl f b [] = b
foldl f b (x ∷ xs) = foldl f (f b x) xs

open import Data.Nat

length : List A → ℕ
length = foldr (λ _ → suc) zero

open import Data.Fin

infixl 6 _!!_
_!!_ : (xs : List A) → Fin (length xs) → A
(x ∷ xs) !! fzero  = x
(x ∷ xs) !! fsuc n = xs !! n

open import Data.Maybe

infixl 6 _!?_
_!?_ : (xs : List A) → ℕ → Maybe A
[]       !? n     = nothing
(x ∷ xs) !? zero  = just x
(x ∷ xs) !? suc n = xs !? n

open import Data.Sigma

open import Function

infixr 5 _++_
_++_ : List A → List A → List A
_++_ = flip (foldr _∷_)

mapl : (A → B) → List A → List B
mapl f = foldr (_∷_ ∘ f) []

concatMap : (A → List B) → List A → List B
concatMap f = foldr (_++_ ∘ f) []
