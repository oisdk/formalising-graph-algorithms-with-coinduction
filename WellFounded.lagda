\begin{code}
{-# OPTIONS --cubical --safe #-}

module WellFounded where

open import Level

data Acc {a r} {A : Type a} (_≺_ : A → A → Type r) (x : A) : Type (a ℓ⊔ r)

\end{code}
%<*acc-def>
\begin{code}
data Acc _≺_ x where acc : (∀ y → y ≺ x → Acc _≺_ y) → Acc _≺_ x
\end{code}
%</acc-def>
\begin{code}

-- record Acc {a r} {A : Type a} (R : A → A → Type r) (x : A) : Type (a ℓ⊔ r) where
--   inductive
--   constructor acc
--   field step : ∀ y → R y x → Acc R y
-- open Acc public

WellFounded : ∀ {r} → (A → A → Type r) → Type _
\end{code}
%<*well-founded>
\begin{code}
WellFounded _≺_ = ∀ x → Acc _≺_ x
\end{code}
%</well-founded>
\begin{code}

open import HLevels
open import Path

isPropAcc : ∀ {r} {R : A → A → Type r} {x : A} → isProp (Acc R x)
isPropAcc (acc x) (acc y) = cong acc (funExt λ n → funExt λ p → isPropAcc (x n p) (y n p))

module _ {A : Type a} {B : Type b} {r} (f : A → B) {_≺_ : B → B → Type r} where
  private
    _≺′_ : A → A → Type r
    x ≺′ y = f x ≺ f y

  module _ (wellFounded : WellFounded _≺_) where
    fun-wellFounded′ : ∀ x → Acc _≺_ (f x) → Acc _≺′_ x
    fun-wellFounded′ x (acc wf) = acc λ y y<x → fun-wellFounded′ y (wf (f y) y<x)

    fun-wellFounded : WellFounded _≺′_
    fun-wellFounded x = fun-wellFounded′ x (wellFounded (f x))
\end{code}
