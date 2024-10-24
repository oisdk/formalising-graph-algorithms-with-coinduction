{-# OPTIONS --safe #-}

module Also where

open import Level
open import Path

record AlsoCalled {A : Type a} (x y : A) : Type a where
  field the-same : x ≡ y
open AlsoCalled ⦃ ... ⦄ public

instance
  obviouslyTheSame : {x : A} → AlsoCalled x x
  obviouslyTheSame .the-same = refl

-- This is a way to write the same expression twice, to allow inline
-- evaluation for readability purposes.
infixr 1 _,⦂_
_,⦂_ : (x y : A) → ⦃ _ : AlsoCalled x y ⦄ → A
x ,⦂ y = x

private module AlsoExamples where
  open import Data.Bool
  open import Function

  Boolean Truthy : Type
  Boolean = Bool
  Truthy = Bool

  _ : Bool ,⦂ Boolean
  _ = true ⦂ Bool ⦂ Truthy ,⦂ Boolean ,⦂ Truthy ⦂ Bool ,⦂ Boolean
