\begin{code}

open import Prelude
open import Algebra.Monus

module Unsafe.WeightedGraphs {W : Type} (mon : TMAPOM W) where

open import WeightedGraphs mon

{-# NON_TERMINATING #-}
\end{code}
%<*star>
\begin{code}[number=eqn:star-bfs]
_∗ : GraphOf A → GraphOf A
g ∗ = 𝟙 ⊕ (g ∗ ⊗ g)
\end{code}
%</star>
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
%<*star-alt>
\begin{code}[number=eqn:star-dfs]
_∗′ : GraphOf A → GraphOf A
g ∗′ = 𝟙 ⊕ (g ⊗ g ∗′)
\end{code}
%</star-alt>
