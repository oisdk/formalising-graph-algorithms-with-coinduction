\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude hiding (map₂)
open import Algebra.Monus

module Unsafe.Codata.Pairing {S : Type} (mon : TMAPOM S) where

open import Codata.Pairing mon hiding (search)
open import Codata.Chain S
open import Data.Link S

private module Search1 {A : Type} where
\end{code}
%<*search-hole-1>
\begin{code}
  search : Heap A → Chain A
  search = ana ({!!} ⦂ Heap A →′ A × Link (Heap A))
\end{code}
%</search-hole-1>
%<*map2-sig>
\begin{code}
map₂ : (A → B) → C × A → C × B
\end{code}
%</map2-sig>
\begin{code}
map₂ f (z , x) = z , f x

private module Search2 {A : Type} where
\end{code}
%<*search-hole-2>
\begin{code}
  search : Heap A → Chain A
  search = ana (map₂ ({!!} ⦂ List (S × Heap A) →′ Link (Heap A)) ∘ out)
\end{code}
%</search-hole-2>
