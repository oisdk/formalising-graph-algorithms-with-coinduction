{-# OPTIONS --safe #-}

module HITs.PropositionalTruncation where

open import Cubical.HITs.PropositionalTruncation
  using ()
  renaming
    ( squash₁ to squash
    ; ∥_∥₁ to ∥_∥
    ; ∣_∣₁ to ∣_∣
    ; elim to ∥elim∥
    ; rec→Set to ∥rec∥→Set
    )
  public

open import Level
open import HLevels

infixr -1 ∥rec∥
∥rec∥ : isProp B → (A → B) → ∥ A ∥ → B
∥rec∥ = Cubical.HITs.PropositionalTruncation.rec

syntax ∥rec∥ is-prop (λ v → e) wrapped = ∥let ⟨ is-prop ⟩ v ≔ wrapped in∥ e

-- elim : {P : ∥ A ∥₁ → Type ℓ} → ((a : ∥ A ∥₁) → isProp (P a))
--      → ((x : A) → P ∣ x ∣₁) → (a : ∥ A ∥₁) → P a
-- elim Pprop f ∣ x ∣₁ = f x
-- elim Pprop f (squash₁ x y i) =
--   isOfHLevel→isOfHLevelDep 1 Pprop
--     (elim Pprop f x) (elim Pprop f y) (squash₁ x y) i

∥map∥ : (A → B) → ∥ A ∥ → ∥ B ∥
∥map∥ f = ∥rec∥ squash (λ x → ∣ f x ∣)

∥liftA2∥ : (A → B → C) → ∥ A ∥ → ∥ B ∥ → ∥ C ∥
∥liftA2∥ f = ∥rec∥ (isProp→ squash) (λ x → ∥map∥ (f x))

