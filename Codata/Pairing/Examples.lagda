\begin{code}
{-# OPTIONS --safe #-}

open import Prelude
open import Algebra.Monus

module Codata.Pairing.Examples {S : Type} (mon : TMAPOM S) where

open TMAPOM mon
open import Codata.Chain S
open import Codata.Pairing mon

GraphOf : Type a → Type a
GraphOf V = V → List (S × V)

trace : GraphOf A → A → Heap A
trace g = hana (λ x → x , g x)


\end{code}
