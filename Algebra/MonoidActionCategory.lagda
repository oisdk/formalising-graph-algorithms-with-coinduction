\begin{code}
{-# OPTIONS --safe #-}

open import Algebra hiding (RightAction)
open import Prelude hiding (∣_∣; ∥_∥)

module Algebra.MonoidActionCategory {M : Type} (mon : Monoid M) where

open Monoid mon

record Action (A : Type a) : Type a where
  infixl 5 _·_
  field
    _·_ : A → M → A
    act : ∀ x y z → (x · y) · z ≡ x · (y ∙ z)
    ε· : ∀ x → x · ε ≡ x

open Action ⦃ ... ⦄

record Ob : Type₁ where
  constructor ∥_∥
  field
    ∣_∣ : Type
    ⦃ acts ⦄ : Action ∣_∣
open Ob

_⟶_ : Ob → Ob → Type _
X ⟶ Y = Σ[ f ⦂ ∣ X ∣ →′ ∣ Y ∣ ] × ∀ x y → f x · y ≡ f (x · y)

private variable X Y Z : Ob

id′ : X ⟶ X
id′ .fst = id
id′ .snd x y = refl

_⊚_ : (Y ⟶ Z) → (X ⟶ Y) → X ⟶ Z
(f ⊚ g) .fst = f .fst ∘ g .fst
(f ⊚ g) .snd x y = f .snd (g .fst x) y ; cong (f .fst) (g .snd x y)

instance
  selfAction : Action M 
  selfAction ._·_ = _∙_
  selfAction .act = assoc
  selfAction .ε· = ∙ε

Rep : Ob → Type
Rep X = ∥ M ∥ ⟶ X

open import Cubical.Data.Sigma using (Σ≡Prop)

Rep-iso : isSet ∣ X ∣ →
\end{code}
%<*rep-iso>
\begin{code}
  (∥ M ∥ ⟶ X) ⇔ ∣ X ∣
\end{code}
%</rep-iso>
\begin{code}
Rep-iso _ .fun (f , _) = f ε
Rep-iso _ .inv x .fst y = x · y
Rep-iso _ .inv x .snd = act x
Rep-iso _ .rightInv = ε· 
Rep-iso {X = X} isSetX .leftInv  (f , p) =
  Σ≡Prop
    (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSetX  _ _ )
    (funExt λ x → p ε x ; cong f (ε∙ x))
\end{code}
