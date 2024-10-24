{-# OPTIONS --safe #-}

module Data.Fin where

open import Level
open import Data.Nat
open import Data.Empty
open import Data.Maybe

private
  variable n : ℕ

Fin : ℕ → Type
Fin zero    = ⊥
Fin (suc n) = Maybe (Fin n)

pattern fzero = nothing
pattern fsuc i = just i

open import Decidable
open import Data.Bool
open import Path
open import Discrete
open import Discrete.IsSet

module DiscreteFin where
  _≡ᴮ_ : Fin n → Fin n → Bool
  _≡ᴮ_ {n = suc n} fzero fzero = true
  _≡ᴮ_ {n = suc n} (fsuc x) (fsuc y) = x ≡ᴮ y
  _≡ᴮ_ {n = suc n} _ _ = false

  sound : (x y : Fin n) → T (x ≡ᴮ y) → x ≡ y
  sound {n = suc _} fzero    fzero    p = refl
  sound {n = suc _} (fsuc x) (fsuc y) p = cong fsuc (sound x y p)

  complete : (x : Fin n) → T (x ≡ᴮ x)
  complete {n = suc _} fzero    = _
  complete {n = suc _} (fsuc x) = complete x

discreteFin : Discrete (Fin n)
discreteFin = from-bool-eq record { DiscreteFin }

open import HLevels

isSetFin : isSet (Fin n)
isSetFin = Discrete→isSet discreteFin

open import Literals.Number
open import Agda.Builtin.Nat renaming (_<_ to _<ᵇ_)
open import Data.Bool

FinFromℕ : ∀ m n → T (m <ᵇ n) → Fin n
FinFromℕ zero    (suc n) p = fzero
FinFromℕ (suc m) (suc n) p = fsuc (FinFromℕ m n p)

instance
  numberFin : ∀ {n} → Number (Fin n)
  numberFin {n} = record
    { Constraint = λ m → T (m <ᵇ n)
    ; fromNat    = λ m {{pr}} → FinFromℕ m n pr
    }

open import Data.Unit

_ : Fin 5
_ = 3

_ : Fin 1
_ = 0
