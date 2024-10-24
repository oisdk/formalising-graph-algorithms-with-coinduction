\begin{code}
{-# OPTIONS --safe #-}

module Data.Vert where

open import Prelude hiding (a; b; c)

\end{code}
%<*vert>
\begin{code}
data Vert : Type where
  a b c d : Vert
\end{code}
%</vert>
\begin{code}
module VertDiscrete where
  _≡ᴮ_ : Vert → Vert → Bool
  a ≡ᴮ a = true
  b ≡ᴮ b = true
  c ≡ᴮ c = true
  d ≡ᴮ d = true
  _ ≡ᴮ _ = false

  sound : ∀ x y → T (x ≡ᴮ y) → x ≡ y
  sound a a p = refl
  sound b b p = refl
  sound c c p = refl
  sound d d p = refl

  complete : ∀ x → T (x ≡ᴮ x)
  complete a = tt
  complete b = tt
  complete c = tt
  complete d = tt

discreteVert : Discrete Vert
discreteVert = from-bool-eq (record { VertDiscrete })
\end{code}
