{-# OPTIONS --safe #-}

module Data.List.Snoc where

open import Prelude

open import Data.List using ([]) public
import Data.List as Cons

infixl 5 _∹_
pattern _∹_ xs x = x List.∷ xs
