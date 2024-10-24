{-# OPTIONS --safe #-}

open import Algebra.Monus
open import Prelude
open import Algebra

module Data.Weighted.Semimodule {ℓ} {S : Type ℓ}  (mon : TMAPOM S) where

open TMAPOM mon hiding (commutativeMonoid)

open import Data.Weighted.Definition ⊓-semigroup
open import Data.Weighted.Eliminators ⊓-semigroup
open import Data.Weighted.CommutativeMonoid ⊓-semigroup
open import Data.Weighted.Monad (weight S tapom) renaming (_⋊_ to _⋊′_)
open import Data.Weighted.Functor

module WeightedSemimodule {A : Type a} where
  semimodule : CommutativeMonoid (Weighted A)
  semimodule = commutativeMonoid

  _⋊_ : S → Weighted A → Weighted A
  _⋊_ = _⋊′_

  ⟨*⟩⋊ : ∀ x y z → (x ∙ y) ⋊ z ≡ x ⋊ (y ⋊ z)
  ⟨+⟩⋊ : ∀ x y z → (x ⊓ y) ⋊ z ≡ (x ⋊ z) ∪ (y ⋊ z)
  1⋊ : Identityˡ _⋊_ ε

  ⋊∅ : ∀ x → x ⋊ ⟅⟆ ≡ ⟅⟆

  ⟨*⟩⋊ x y z = sym (⋊-assoc x y z)
  ⟨+⟩⋊ x y z = sym (⊕⟨⋊⟩ x y z)

  1⋊   =  ε⋊
  ⋊∅   x = refl

weightedSemimodule : WeightSemimodule (weight S tapom) (Weighted A)
weightedSemimodule {A = A} = record { WeightedSemimodule {A = A} ; ⋊⟨∪⟩ = ⋊⟨∪⟩ }
