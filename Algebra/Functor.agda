{-# OPTIONS --safe #-}

module Algebra.Functor where

open import Prelude
open import Algebra

instance
  functor-× : {A : Type a} → Functor {ℓ₁ = b} (A ×_)
  functor-× .Functor.map f (x , y) = x , f y
  functor-× .Functor.map-id _ = refl
  functor-× .Functor.map-comp _ _ _ = refl
