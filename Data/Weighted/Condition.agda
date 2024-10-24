{-# OPTIONS --safe #-}

open import Algebra
open import Prelude

module Data.Weighted.Condition {ℓ} {𝑆 : Type ℓ} (sgp : Semigroup 𝑆) where

open import Data.Weighted.Definition sgp
open import Data.Weighted.Eliminators sgp
open import Data.Weighted.Functor
open import Data.Weighted.CommutativeMonoid sgp

open Semigroup sgp

module _ {A : Type a} (f : 𝑆 → 𝑆) (f-hom : ∀ p q → f p ∙ f q ≡ f (p ∙ q)) where
  cond-alg : A ⟶W A
  cond-alg = record
    { act-w = λ w x → f w ▹ x ∷ ⟅⟆
    ; coh-w = λ p q x → dup (f p) (f q) x ⟅⟆ ; cong (_▹ x ∷ ⟅⟆) (f-hom p q)
    }

  cond : Weighted A → Weighted A
  cond = [ cond-alg ]W↓
