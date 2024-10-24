\begin{code}
{-# OPTIONS --no-positivity-check #-}
module Unsafe.Codata.Inf where

open import Prelude
open import Unsafe.Codata.Fix

_∞′_ :  (Type a → Type a) → Type a → Type a
\end{code}
%<*inf-def>
\begin{code}
F ∞′ A = ν X ． (F X ⊎ A)
\end{code}
%</inf-def>
\begin{code}
_∞ :  (Type a → Type a) → Type a → Type a
(F ∞) A = ν X ． F X ⊎ A
\end{code}
