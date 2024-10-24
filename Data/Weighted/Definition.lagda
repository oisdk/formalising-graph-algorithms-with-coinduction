\begin{code}
{-# OPTIONS --safe #-}

open import Algebra
open import Level

module Data.Weighted.Definition {ℓ} {𝑆 : Type ℓ} (sgp : Semigroup 𝑆) where

open Semigroup sgp renaming (_∙_ to _⊓_)

open import Path
open import HLevels

infixr 5 _▹_∷_

data Weighted (A : Type a) : Type (a ℓ⊔ ℓ)

\end{code}
%<*head>
\begin{code}
data Weighted A where
\end{code}
%</head>
%<*point>
\begin{code}
  ⟅⟆     :  Weighted A
  _▹_∷_  :  (p : 𝑆) (x : A) (xs : Weighted A) → Weighted A
\end{code}
%</point>
%<*com>
\begin{code}
  com  : ∀ p x q y xs  → p ▹ x ∷ q ▹ y ∷ xs  ≡ q ▹ y ∷ p ▹ x ∷ xs
\end{code}
%</com>
%<*dup>
\begin{code}
  dup  : ∀ p q x xs → p ▹ x ∷ q ▹ x ∷ xs  ≡ p ⊓ q ▹ x ∷ xs
\end{code}
%</dup>
%<*trunc>
\begin{code}
  trunc : ∀ xs ys (p q : xs ≡ ys) → p ≡ q
\end{code}
%</trunc>
