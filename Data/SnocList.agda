{-# OPTIONS --safe #-}

module Data.SnocList where

open import Prelude hiding ([_])
import Data.List as L
open import Data.List
  using ([]) public

open import Data.NonEmpty
  using (List⁺; not-empty)
  renaming (tail to init; head to last)
  public
import Data.NonEmpty as NEL

infixl 5 _∹_
pattern _∹_ xs x = x L.∷ xs
pattern _∹_ xs x = x NEL.∷ xs

infixl 5 _∹′_
_∹′_ : List⁺ A → A → List⁺ A
(xs ∹′ x) .init = not-empty xs
(xs ∹′ x) .last = x

open import Data.List.Syntax using (VecT)
import Data.List.Syntax

[_] : ∀ {n} → VecT n A → List⁺ A
[_] {n = zero}  x = [] ∹ x
[_] {n = suc n} (x , xs) = foldl  _∹′_ ([] ∹ x) (Data.List.Syntax.[ xs ])

_ : [ 1 , 2 , 3 ] ≡ [] ∹ 1 ∹ 2 ∹ 3
_ = refl
