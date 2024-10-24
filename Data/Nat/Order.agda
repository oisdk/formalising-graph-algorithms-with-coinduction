{-# OPTIONS --safe #-}

module Data.Nat.Order where

open import Data.Nat
open import Agda.Builtin.Nat renaming (_<_ to _<ᵇ_)
open import Prelude
open import Data.Bool

infix 4 _<_ _≤ᵇ_ _≤_ _≤?_

_<_ : ℕ → ℕ → Type
n < m = T (n <ᵇ m)

_≤ᵇ_ : ℕ → ℕ → Bool
n ≤ᵇ m = n <ᵇ suc m

_≤_ : ℕ → ℕ → Type
n ≤ m = T (n ≤ᵇ m)

_≤?_ : ∀ n m → Dec (n ≤ m)
n ≤? m = T? _

≰⇒> : ∀ n m → ¬ (n ≤ m) → m < n
≰⇒> zero zero p = p tt
≰⇒> zero (suc m) p = p tt
≰⇒> (suc n) zero p = tt
≰⇒> (suc n) (suc m) p = ≰⇒> n m p

<⇒≤ : ∀ n m → n < m → n ≤ m
<⇒≤ zero m p = tt
<⇒≤ (suc n) zero p = p
<⇒≤ (suc n₁) (suc n) p = <⇒≤ n₁ n p
