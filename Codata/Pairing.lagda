\begin{code}
{-# OPTIONS --safe #-}

open import Prelude
open import Algebra
open import Algebra.Monus

module Codata.Pairing {S : Type} (mon : TMAPOM S) where

open TMAPOM mon
open import Codata.Chain S

infixr 5 _◂_
record Heap (A : Type) : Type where
  coinductive; constructor _◂_
  field  extract  : A
         unwrap   : List (S × Heap A)
open Heap public

out : Heap A → A × List (S × Heap A)
out xs = extract xs , unwrap xs

module _ {A : Type} (ψ : B → A × List (S × B)) where
  hana  : B → Heap A
  hana′ : A × List (S × B) → Heap A
  hana″ : List (S × B) → List (S × Heap A)

  hana = hana′ ∘ ψ

  hana′ (x , xs) .extract = x
  hana′ (x , xs) .unwrap = hana″ xs

  hana″ [] = []
  hana″ ((w , x) ∷ xs) = (w , hana x) ∷ hana″ xs


open import Data.Link S

open import Data.NonEmpty

_⋈_ : S × Heap A → S × Heap A → S × Heap A
(wₗ , lls) ⋈ (wᵣ , rrs) with wₗ ≤|≥ wᵣ
... | inl  (wᵣ∸wₗ  , _)  = wₗ  , extract lls  ◂ (wᵣ∸wₗ  , rrs)  ∷ unwrap lls
... | inr  (wₗ∸wᵣ  , _)  = wᵣ  , extract rrs  ◂ (wₗ∸wᵣ  , lls)  ∷ unwrap rrs

\end{code}
%<*merges-pl>
\begin{code}
merges⁺ :  S × Heap A → List (S × Heap A) 
  →        S × Heap A
merges⁺ x₁  [] = x₁
merges⁺ x₁  (x₂ ∷ []) = x₁ ⋈ x₂
merges⁺ x₁  (x₂ ∷ x₃ ∷ xs) =
  (x₁ ⋈ x₂) ⋈ merges⁺ x₃ xs
\end{code}
%</merges-pl>
%<*merges>
\begin{code}
merges :  List (S × Heap A)
  →       Link (Heap A)
merges [] = ⟨⟩
merges (x ∷ xs) = just (merges⁺ x xs)
\end{code}
%</merges>
\begin{code}

open Functor ⦃...⦄
\end{code}
%<*search>
\begin{code}
search : Heap A → Chain A
search = ana (map₂ merges ∘ out)
\end{code}
%</search>
\begin{code}
private module HeapGraph where
  GraphOf : Type → Type
  GraphOf A = A → List (S × A)

  trace-heap : GraphOf A → A → Heap A
  trace-heap f = hana (λ x → x , f x)
  
  pathed : GraphOf A → GraphOf (List⁺ A)
  pathed g (v ∷ vs) = mapl (map₂ (_∷ v ∷ vs)) (g v)

  filterg : (A → Bool) → GraphOf A → GraphOf A
  filterg p g x = if p x then g x else []

  module _ {V} (disc : Discrete V) where
    open import Data.NonEmpty.Discrete disc

    dijkstra : V → GraphOf V → Chain (List⁺ V)
    dijkstra s g = search (trace-heap (filterg uniq (pathed g)) (s ∷ []))

\end{code}
