{-# OPTIONS --safe #-}

module Data.List.Properties where

open import Prelude
open import Algebra
open import Data.List

foldr-universal : ∀ (h : List B → A) f e
                → (h [] ≡ e)
                → (∀ x xs → h (x ∷ xs) ≡ f x (h xs))
                → ∀ xs → h xs ≡ foldr f e xs
foldr-universal h f e base step [] = base
foldr-universal h f e base step (x ∷ xs) =
  step x xs ; cong (f x) (foldr-universal h f e base step xs)

foldr-id : (xs : List A) → xs ≡ foldr _∷_ [] xs
foldr-id = foldr-universal id _∷_ [] refl (λ _ _ → refl)

foldr-fusion : ∀ (f : C → A) {_⊕_ : B → C → C} {_⊗_ : B → A → A} e
              → (∀ x y → f (x ⊕ y) ≡ x ⊗ f y)
              → ∀ xs → f (foldr _⊕_ e xs) ≡ foldr _⊗_ (f e) xs
foldr-fusion h {f} {g} e fuse =
  foldr-universal (h ∘ foldr f e) g (h e) refl (λ x xs → fuse x (foldr f e xs))

lmap : (A → B) → List A → List B
lmap f = foldr (_∷_ ∘ f) []

functorList : Functor {ℓ₁ = a} List
functorList .Functor.map = lmap
functorList .Functor.map-id = sym ∘′ foldr-id
functorList .Functor.map-comp f g = foldr-fusion (lmap f) [] λ x y → refl

all : (A → Bool) → List A → Bool
all p = foldr (_&&_ ∘ p) true

infixr 5 _∈_ _∉_

_∈_ : A → List A → Type _
x ∈ xs = ∃ i × (xs !! i ≡ x)

_∉_ : A → List A → Type _
x ∉ xs = ¬ (x ∈ xs)

there : ∀ (y : A) {x} {xs : List A} → x ∈ xs → x ∈ y ∷ xs
there _ (i , p) = fsuc i , p
