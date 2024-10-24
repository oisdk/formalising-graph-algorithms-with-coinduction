\begin{code}
{-# OPTIONS --safe #-}

open import Prelude
open import Algebra
open import Algebra.Monus

module Data.Pairing {S : Type} (mon : TMAPOM S) where

open TMAPOM mon

infixr 5 _◂_
record Heap (A : Type) : Type where
  inductive; constructor _◂_; pattern
  field
    extract : A
    unwrap : List (S × Heap A)
open Heap
\end{code}
%<*merge-diff>
\begin{code}
_⋈_ : S × Heap A → S × Heap A → S × Heap A
(wₗ , l ◂ ls) ⋈ (wᵣ , r ◂ rs) = if does (wₗ ≤? wᵣ)  then  wₗ  , l  ◂ (wᵣ ∸ wₗ  , r  ◂ rs)  ∷ ls
                                                    else  wᵣ  , r  ◂ (wₗ ∸ wᵣ  , l  ◂ ls)  ∷ rs
\end{code}
%</merge-diff>
