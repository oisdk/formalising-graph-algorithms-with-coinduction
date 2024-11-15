\begin{code}
{-# OPTIONS --safe #-}

open import Prelude hiding (a; b; c; id; [_]) renaming (A to V)
open import Algebra
open import Algebra.Monus

module NeighboursGraphs where

open import Data.Nat.Monus
open TMAPOM nat-mon hiding (_≟_)
open import Codata.Neighbours nat-wfmon
open import Data.Vert
open import Data.SnocList

\end{code}
%<*graph-of>
\begin{code}[number=eqn:graphof]
GraphOf : Type → Type
GraphOf V = V → Neighbours V
\end{code}
%</graph-of>
\begin{code}
module _ where
  open import Codata.Neighbours.Syntax nat-wfmon
  private module GraphSnippets where
    graph : GraphOf Vert
\end{code}
%<*graph-a>
\begin{code}
    graph a = ⟅ 7 ▹ b , 2 ▹ c ⟆
\end{code}
%</graph-a>
\begin{code}
    graph _ = ⟅⟆

  private module DisplayCollatz where
    open import Data.Nat
    open import Data.Nat.Properties
    open import Agda.Builtin.Nat using (_*_; _-_)
    infix 4 _≟_
    _≟_ = discreteℕ

\end{code}
%<*collatz>
\begin{code}[number=eqn:collatz]
    collatz : GraphOf ℕ
    collatz 0  = ⟅⟆
    collatz n  = 
      if does (n mod 6 ≟ 4)
        then  ⟅ 1 ▹ 2 * n , 1 ▹ (n - 1) div 3 ⟆
        else  ⟅ 1 ▹ 2 * n ⟆
\end{code}
%</collatz>
\begin{code}
  module _ where
    open import Data.Nat
    open import Data.Nat.Properties
    open import Agda.Builtin.Nat using (_*_; _-_)
    infix 4 _≟_
    _≟_ = discreteℕ

    collatz : GraphOf ℕ
    collatz 0 = ⟅⟆
    collatz n =
      if does (n mod 6 ≟ 4)
        then  ⟅ 0 ▹ 2 * n , 0 ▹ (n - 1) div 3 ⟆
        else  ⟅ 0 ▹ 2 * n ⟆

  module NonIdealGraph where
\end{code}
%<*example-wgraph>
\begin{code}
    graph : GraphOf Vert
    graph a  = ⟅ 7 ▹ b , 2 ▹ c ⟆
    graph b  = ⟅ 1 ▹ c ⟆
    graph c  = ⟅ 3 ▹ d , 1 ▹ b ⟆
    graph d  = ⟅ 5 ▹ b ⟆
\end{code}
%</example-wgraph>
\begin{code}
  graph : Vert → INeighbours Vert
  graph a  = ⟅ 6 ▹ b , 1 ▹ c ⟆
  graph b  = ⟅ 0 ▹ c ⟆
  graph c  = ⟅ 2 ▹ d , 0 ▹ b ⟆
  graph d  = ⟅ 4 ▹ b ⟆
\end{code}
%<*filtering>
\begin{code}[number=eqn:filtering]
  filtering : (V → Bool) → GraphOf V
  filtering p v = if p v then ⟅ 0 ▹ v ⟆ else ⟅⟆
\end{code}
%</filtering>
%<*pathed>
\begin{code}[number=eqn:pathed]
pathed : GraphOf V → GraphOf (List⁺ V)
pathed g (vs ∹ v) =
  mapₙ (λ t → vs ∹ v ∹ t) (g v)
\end{code}
%</pathed>
\begin{code}

open import Codata.Neighbours.Monad nat-wfmon
open import Data.Weighted ⊓-semigroup
open Monad neighboursMonad using (_>=>_)
open import Data.Nat.Properties using (suc≢zero)
open import Codata.Neighbours.Solves nat-wfmon (suc zero) suc≢zero using (_∗)
open import Data.Weighted.Syntax ⊓-semigroup
open import Data.Set using (𝒦; _∷_; ∅)


module Hamiltonian {V : Type} (disc : Discrete V) (Dom : 𝒦 V) where
  open import Data.NonEmpty.Discrete disc renaming (covers to covers′)

  covers : List⁺ V → Bool
  covers = covers′  Dom
  
\end{code}
%<*hamiltonian>
\begin{code}[number=eqn:hamiltonian]
  hamiltonian : GraphOf V → GraphOf (List⁺ V)
  hamiltonian g = (pathed g >=> filtering uniq) ∗ >=> filtering covers
\end{code}
%</hamiltonian>
\begin{code}
open Hamiltonian discreteVert (a ∷ b ∷ c ∷ d ∷ ∅)
\end{code}
%<*paths>
\begin{code}
paths : GraphOf (List⁺ Vert)
paths = hamiltonian graph
\end{code}
%</paths>

\begin{code}
_ :
\end{code}
%<*paths-a>
\begin{code}
    hamiltonian graph [ a ] ⊩ 15 ≡ ⟅ 11 ▹ [ a , b , c , d ] , 10 ▹ [ a , c , d , b ] ⟆
\end{code}
%</paths-a>
\begin{code}
_ = refl

module _ where
  open import Data.NonEmpty.Discrete discreteVert
\end{code}
%<*dijkstra>
\begin{code}
  dijkstra : Vert → GraphOf Vert → Neighbours (List⁺ Vert)
  dijkstra s g = ((pathed g >=> filtering uniq) ∗) [ s ]
\end{code}
%</dijkstra>

\begin{code}
module _ where
  open import Data.Nat.Properties
  open import Data.NonEmpty.Discrete discreteℕ

  _ :
\end{code}
%<*collatz-paths>
\begin{code}
    ((pathed collatz >=> filtering uniq) ∗) [ 1 ] ⊩ 5 ≡  
       ⟅ 0  ▹ [ 1 ] , 1  ▹ [ 1 , 2 ] , 2  ▹ [ 1 , 2 , 4 ]
       , 3  ▹ [ 1 , 2 , 4 , 8 ] , 4  ▹ [ 1 , 2 , 4 , 8 , 16 ]
       , 5  ▹ [ 1 , 2 , 4 , 8 , 16 , 32 ]
       , 5  ▹ [ 1 , 2 , 4 , 8 , 16 , 5 ] ⟆
\end{code}
%</collatz-paths>
\begin{code}
  _ = refl
  -- _ = refl
\end{code}
