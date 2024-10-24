\begin{code}
{-# OPTIONS --safe #-}

open import Prelude
open import Algebra

module Data.Link {ℓ} (𝑆 : Type ℓ) where

infixr 5 _∝_

Link : Type a → Type (ℓ ℓ⊔ a)
\end{code}
%<*link>
\begin{code}
Link A = Maybe (𝑆 × A)
\end{code}
%</link>
%<*link-patt>
\begin{code}
pattern _∝_ p x = just (p , x)
pattern ⟨⟩ = nothing
\end{code}
%</link-patt>
\begin{code}

lmap : (A → B) → Link A → Link B
lmap f ⟨⟩ = ⟨⟩
lmap f (p ∝ x) = p ∝ f x

instance
  functorLink : Functor {ℓ₁ = a} Link
  functorLink .Functor.map f nothing = nothing
  functorLink .Functor.map f (just (p , x)) = just (p , f x)
  functorLink .Functor.map-id nothing = refl
  functorLink .Functor.map-id (just _) = refl
  functorLink .Functor.map-comp f g nothing = refl
  functorLink .Functor.map-comp f g (just _) = refl
\end{code}
