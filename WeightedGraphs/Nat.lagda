\begin{code}
{-# OPTIONS --safe #-}

open import Prelude hiding (a; b; c; id; _∷_)
open import Algebra
open import Algebra.Monus

module WeightedGraphs.Nat where

open import Data.Nat.Monus
open TMAPOM nat-mon
open import Data.Weighted ⊓-semigroup
open import Data.Weighted.Monad (weight ℕ tapom)
open import Data.Weighted.Syntax ⊓-semigroup
open import Data.Vert
open import WeightedGraphs nat-mon

graph : GraphOf Vert
graph a  = ⟅ 7 ▹ b , 2 ▹ c ⟆
graph b  = ⟅ 1 ▹ c ⟆
graph c  = ⟅ 3 ▹ d , 1 ▹ b ⟆
graph d  = ⟅ 5 ▹ b ⟆

_ : ⟅ 7 ▹ b , 2 ▹ c ⟆ ≡ ⟅ 2 ▹ c , 7 ▹ b ⟆
_ = 
\end{code}
%<*com-a-edges>
\begin{code}
  com 7 b 2 c  ⟅⟆ ⦂ ⟅ 7 ▹ b , 2 ▹ c ⟆ ≡ ⟅ 2 ▹ c , 7 ▹ b ⟆
\end{code}
%</com-a-edges>
\begin{code}
private module ConnectionDemo where
  f : GraphOf Vert
\end{code}
%<*f-graph>
\begin{code}
  f a  = ⟅ 1 ▹ b , 2 ▹ c ⟆
  f b  = ⟅ 2 ▹ d ⟆
  f _  = ⟅⟆
\end{code}
%</f-graph>
\begin{code}

  g : GraphOf Vert
\end{code}
%<*g-graph>
\begin{code}
  g b  = ⟅ 1 ▹ a , 3 ▹ d ⟆
  g c  = ⟅ 4 ▹ d ⟆
  g _  = ⟅⟆
\end{code}
%</g-graph>
\begin{code}

  _ : f >=> g ≡ λ { a → ⟅ 2 ▹ a , 4 ▹ d ⟆ ; _ → ⟅⟆ }
  _ = funExt
    λ { a → cong (2 ▹ a ∷_) (dup 4 6 d ⟅⟆)
      ; b → refl
      ; c → refl
      ; d → refl
      }
\end{code}
