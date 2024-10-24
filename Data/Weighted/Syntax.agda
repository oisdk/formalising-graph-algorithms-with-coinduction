{-# OPTIONS --safe #-}

open import Algebra
open import Level

module Data.Weighted.Syntax {ℓ} {𝑆 : Type ℓ} (sgp : Semigroup 𝑆) where

open Semigroup sgp renaming (_∙_ to _⊕_)

open import Path
open import HLevels
open import Data.Weighted.Definition sgp

open import Prelude hiding ([_]; _∷_)

infixr 5 _▹_
record WithWeight (A : Type a) : Type (ℓ ℓ⊔ a) where
  constructor _▹_
  field
    weight-of : 𝑆
    value  : A
open WithWeight public

VecT : ℕ → Type a → Type (a ℓ⊔ ℓ)

VecT zero    A = WithWeight A
VecT (suc n) A = WithWeight A × VecT n A

⟅_⟆ : ∀ {n} → VecT n A → Weighted A
⟅_⟆ {n = zero}  (w ▹ x) = w ▹ x ∷ ⟅⟆
⟅_⟆ {n = suc n} (w ▹ x , xs) = w ▹ x ∷ ⟅ xs ⟆


