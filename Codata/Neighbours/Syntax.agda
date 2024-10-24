{-# OPTIONS --safe #-}

open import Prelude hiding ([_]; [])
open import Algebra.Monus

module Codata.Neighbours.Syntax
  {W : Type} (mon : WellFoundedMonus W)
  where

open import Algebra
open WellFoundedMonus mon
open Weight (weight W tapom)

import Data.Weighted

module W = Data.Weighted ⊕-semigroup

open import Data.Weighted.Syntax ⊕-semigroup
  renaming (⟅_⟆ to ⟅_⟆ʷ)
  public

open import Codata.Neighbours mon

⟅_⟆ : ∀ {n} → VecT n A → Neighbours A
⟅_⟆ = searched ∘ ⟅_⟆ʷ

⟅⟆ : Neighbours A
⟅⟆ ⊩ _ = W.⟅⟆
⟅⟆ .neighbourly v w x = refl
