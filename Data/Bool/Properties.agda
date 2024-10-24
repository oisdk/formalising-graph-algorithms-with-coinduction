{-# OPTIONS --safe #-}

module Data.Bool.Properties where

open import Data.Bool
open import Decidable
open import Path
open import Data.Unit
open import HLevels
open import Data.Empty.Properties
open import Data.Unit.Properties
open import Discrete
open import Discrete.IsSet

discreteBool : Discrete Bool
discreteBool = from-bool-eq record
  { _≡ᴮ_ = bool′ neg (λ x → x)
  ; sound = λ { false false p → refl ; true true p → refl } 
  ; complete = λ { false → tt ; true → tt }
  }

isSetBool : isSet Bool
isSetBool = Discrete→isSet discreteBool

isPropT : ∀ b → isProp (T b)
isPropT false = isProp⊥
isPropT true  = isProp⊤

open import Data.Empty

false≢true : false ≢ true
false≢true p = subst (bool ⊤ ⊥) p tt

true≢false : true ≢ false
true≢false p = subst (bool ⊥ ⊤) p tt

or-assoc : ∀ x y z → (x || y) || z ≡ x || (y || z)
or-assoc false y z = refl
or-assoc true  y z = refl

or-idem : ∀ x → x || x ≡ x
or-idem false = refl
or-idem true  = refl

or-comm : ∀ x y → (x || y) ≡ (y || x)
or-comm false false = refl
or-comm false true  = refl
or-comm true  false = refl
or-comm true  true  = refl
