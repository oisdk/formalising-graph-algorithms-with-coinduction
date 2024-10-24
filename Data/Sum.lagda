\begin{code}
{-# OPTIONS --without-K --safe #-}

module Data.Sum where

open import Level
open import Function
open import Data.Sum.Definition public

either : ∀ {ℓ} {C : A ⊎ B → Type ℓ} →  ((a : A) → C (inl a)) → ((b : B) → C (inr b))
        → (x : A ⊎ B) → C x
either f _ (inl x) = f x
either _ g (inr y) = g y

either′ : (A → C) → (B → C) → (A ⊎ B) → C
either′ = either

infixr 8 _▿_
_▿_ = either′

map-⊎ : ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂} {B₁ : Type b₁} {B₂ : Type b₂} →
      (A₁ → A₂) →
      (B₁ → B₂) →
      (A₁ ⊎ B₁) →
      (A₂ ⊎ B₂)
map-⊎ f g = either (inl ∘ f) (inr ∘ g)

mapˡ : (A → B) → A ⊎ C → B ⊎ C
mapˡ f = map-⊎ f id

mapʳ : (A → B) → C ⊎ A → C ⊎ B
mapʳ = map-⊎ id

open import Path

inl-inj : Injective (inl {A = A} {B = B})
inl-inj {y = y} = cong (either′ id (const y))

inr-inj : Injective (inr {A = A} {B = B})
inr-inj {x = x} = cong (either′ (const x) id)

open import Data.Bool

is-l : A ⊎ B → Bool
is-l = either′ (const true) (const false)

open import Data.List using (List; _∷_; []; foldr)
open import Data.Sigma

\end{code}
%<*partition-sig>
\begin{code}
partition :  (A → B ⊎ C) → List A →
             List B × List C
\end{code}
%</partition-sig>
\begin{code}
partition p = foldr ((map₁ ∘ _∷_ ▿ map₂′ ∘ _∷_) ∘ p) ([] , [])

▿-fusion : ∀ {d} {D : Type d} (f : C → D) (g : A → C) (h : B → C) (x : A ⊎ B) → (f ∘ g ▿ f ∘ h) x ≡ f ((g ▿ h) x)
▿-fusion f g h (inl x) = refl
▿-fusion f g h (inr x) = refl
\end{code}

