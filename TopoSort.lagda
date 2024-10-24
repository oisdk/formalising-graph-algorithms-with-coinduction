\begin{code}
{-# OPTIONS --safe  --termination-depth=2 #-}
open import Prelude

module TopoSort {A : Type a} (disc : Discrete A) where

open import Data.Set.Noetherian disc
open import Data.Set.Discrete disc
open import Data.Set
open import Data.RoseTree

GraphOf : Type a → Type a
GraphOf A = A → List A
\end{code}
%<*trace-ty>
\begin{code}
trace : GraphOf A → List A → Forest A
\end{code}
%</trace-ty>
\begin{code}
trace g dom = expand dom ∅ (noeth Dom)
  where
  Dom : 𝒦 A
  Dom = 𝒦-fromList dom

  expand : List A → ∀ seen → NoethAcc Dom seen → List (Tree A)
  expand []        seen na = []
  expand (v ∷ vs)  seen (nacc wf) with v ∈? Dom | v ∈? seen
  ... | yes v∈Dom | no v∉seen =
    (v & expand (g v) (v ∷ seen) (wf v v∈Dom v∉seen)) ∷ expand vs seen (nacc wf)
  ... | _ | _ = expand vs seen (nacc wf)
\end{code}
%<*topo-sort>
\begin{code}
topo-sort  :  GraphOf A
           →  List A → List A
topo-sort g = fst ∘ sort-f ([] , ∅) ∘ trace g
  where mutual
  sort-f :  List A × 𝒦 A → Forest A →
            List A × 𝒦 A
  sort-f ac []        = ac
  sort-f ac (n ∷ ns)  = sort-t n (sort-f ac ns)

  sort-t : Tree A  → List A × 𝒦 A
                   → List A × 𝒦 A
  sort-t (v & cs) (sorted , seen) =
    if does (v ∈? seen)
      then  (sorted , seen)
      else  map₁ (v ∷_)
            (sort-f (sorted , v ∷ seen) cs)
\end{code}
%</topo-sort>
