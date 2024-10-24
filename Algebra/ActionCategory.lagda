\begin{code}
{-# OPTIONS --safe #-}

open import Algebra hiding (RightAction)
open import Prelude hiding (∣_∣; ∥_∥)

module Algebra.ActionCategory {S : Type} (sgp : Semigroup S) where

open Semigroup sgp

record Action (A : Type a) : Type a where
  infixl 5 _·_
  field
    _·_ : A → S → A
    act : ∀ x y z → (x · y) · z ≡ x · (y ∙ z)

open Action ⦃ ... ⦄

record Ob : Type₁ where
  constructor ∥_∥
  field
    ∣_∣ : Type
    ⦃ acts ⦄ : Action ∣_∣
open Ob

_⟶_ : Ob → Ob → Type _
\end{code}
%<*hom>
\begin{code}
X ⟶ Y = Σ[ f ⦂ ∣ X ∣ →′ ∣ Y ∣ ] × ∀ x y → f x · y ≡ f (x · y)
\end{code}
%</hom>
\begin{code}

private variable X Y Z : Ob

id′ : X ⟶ X
id′ .fst = id
id′ .snd x y = refl

_⊚_ : (Y ⟶ Z) → (X ⟶ Y) → X ⟶ Z
(f ⊚ g) .fst = f .fst ∘ g .fst
(f ⊚ g) .snd x y = f .snd (g .fst x) y ; cong (f .fst) (g .snd x y)

instance
  selfAction : Action S
  selfAction ._·_ = _∙_
  selfAction .act = assoc

Rep : Ob → Type
Rep X = ∥ S ∥ ⟶ X
\end{code}
