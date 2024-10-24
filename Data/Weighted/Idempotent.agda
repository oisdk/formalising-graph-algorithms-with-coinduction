{-# OPTIONS --safe #-}

open import Algebra
open import Prelude
open import Path.Reasoning

module Data.Weighted.Idempotent {ℓ} {S : Type ℓ} (sgp : IdempotentSemigroup S) where

open IdempotentSemigroup sgp

open import Data.Weighted.Definition semigroup
open import Data.Weighted.Eliminators semigroup
open import Data.Weighted.CommutativeMonoid semigroup
open import Data.Weighted.Functor

module _ {A : Type a} where
  ∪-idem : ∀ xs → xs ∪ xs ≡ xs
  ∪-idem = ⟦ alg ⟧
    where
    alg : Ψ[ xs ⦂ Weighted A ] ↦ (xs ∪ xs ≡ xs)
    alg .snd = eq-coh
    alg .fst ⟅⟆ = refl
    alg .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
      w ▹ x ∷ xs ∪ w ▹ x ∷ xs ≡˘⟨ cong (w ▹ x ∷_) (∪-cons w x xs xs)  ⟩
      w ▹ x ∷ w ▹ x ∷ xs ∪ xs ≡⟨ dup w w x (xs ∪ xs) ⟩
      w ∙ w ▹ x ∷ xs ∪ xs     ≡⟨ cong₂ (_▹ x ∷_) (idem w) P⟨xs⟩ ⟩
      w ▹ x ∷ xs ∎

  ⊆-uncons : ∀ w x xs ys → w ▹ x ∷ xs ⊆ ys → xs ⊆ ys
  ⊆-uncons w x xs ys w▹x∷xs =
    xs ∪ ys                ≡˘⟨ cong (xs ∪_) w▹x∷xs ⟩
    xs ∪ w ▹ x ∷ xs ∪ ys   ≡˘⟨ ∪-cons w x xs (xs ∪ ys) ⟩
    w ▹ x ∷ xs ∪ xs ∪ ys   ≡˘⟨ cong (w ▹ x ∷_) (∪-assoc xs xs ys) ⟩
    w ▹ x ∷ (xs ∪ xs) ∪ ys ≡⟨ cong (λ e → w ▹ x ∷ e ∪ ys) (∪-idem xs) ⟩
    w ▹ x ∷ xs ∪ ys        ≡⟨ w▹x∷xs ⟩
    ys ∎

  ⊆-refl : ∀ xs → xs ⊆ xs
  ⊆-refl = ∪-idem
