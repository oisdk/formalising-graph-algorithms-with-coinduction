{-# OPTIONS --safe #-}

module Data.List.Snoc.Syntax where

open import Prelude hiding ([_]; _∷_)
open import Data.List.Snoc
open import Data.List
open import Data.List.Syntax renaming ([_] to [_]ᶜ)

[_] : ∀ {n} → VecT n A → List A
[_] = foldl _∹_ [] ∘ [_]ᶜ
