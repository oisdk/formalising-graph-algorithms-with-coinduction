\begin{code}
{-# OPTIONS --safe #-}

open import Prelude
open import Algebra
open import Algebra.Monus

module Codata.Bush {W : Type} (mon : WellFoundedMonus W) where

open WellFoundedMonus mon

open Weight (weight W tapom)

open import Data.Weighted ⊕-semigroup hiding (⟪_⟫)
open import Data.Weighted.Monad (weight W tapom) hiding (_>>=_; return)
import Data.Weighted.Monad (weight _ tapom) as WB

open import Codata.Chain W

record Forest∞ (A : Type) : Type where
  coinductive; constructor ⟪_⟫
  field out : (W × List (Forest∞ A)) ⊎ A
open Forest∞ public

Forest : Type → Type
Forest = List ∘ Forest∞

private variable s : W

foldWeight : (A → Weighted B) → List A → Weighted B
foldWeight f = foldr (_∪_ ∘ f) ⟅⟆

module _ {A : Type} {s : W} where

  open Reasoning
  
  mutual
    depth  : ∀ w → Acc [ s ]_≺_ w
           → Forest A → Weighted A
    depth w wf =
      foldr (_∪_ ∘ (step w wf ▿ return) ∘ out) ⟅⟆
      where
      return = WB.return

    step  : ∀ w → Acc [ s ]_≺_ w
          → W × Forest A → Weighted A
    step w wf (v , _) with s ≤? v | v ≤? w
    ... | no _ | _ = ⟅⟆
    ... | _ | no _ = ⟅⟆
    step w (acc wf) (v , x) | yes s≤v | yes (k , w≡v∙k) =
        depth k (wf k ≲[ ≤[ ≤-cong k s≤v ] ≲; ≡[ comm k v ] ≲; ≡[ sym w≡v∙k ] ]) x

\end{code}
%<*cutoff-sig>
\begin{code}[number=code:cutoff-sig]
_∣_⊢_  : Forest A → Step → W → Weighted A
\end{code}
%</cutoff-sig>
\begin{code}
xs ∣ s ⊢ w = depth w (well-founded s w) xs

Equiv-UpTo : Forest A → Forest A → Type
\end{code}
%<*equiv-def>
\begin{code}
Equiv-UpTo xs ys =
  ∀ s w → xs ∣ s ⊢ w ≡ ys ∣ s ⊢ w
\end{code}
%</equiv-def>
\begin{code}

Bush : Type → Type
\end{code}
%<*bush>
\begin{code}[number=bush]
Bush A = Forest A / Equiv-UpTo
\end{code}
%</bush>
\begin{code}

open import Data.Link W

\end{code}
%<*merge>
\begin{code}
_⋈_ :  W × Forest A → W × Forest A →
       W × Forest A
(wₗ , ls) ⋈ (wᵣ , rs) with wₗ ≤|≥ wᵣ
... | inl  (wᵣ∸wₗ  , _) = wₗ  , ⟪ inl (wᵣ∸wₗ  , rs)  ⟫ ∷ ls
... | inr  (wₗ∸wᵣ  , _) = wᵣ  , ⟪ inl (wₗ∸wᵣ  , ls)  ⟫ ∷ rs
\end{code}
%</merge>
\begin{code}
merges⁺ : W × Forest A → List (W × Forest A) → W × Forest A
merges⁺ x₁ [] = x₁
merges⁺ x₁ (x₂ ∷ []) = x₁ ⋈ x₂
merges⁺ x₁ (x₂ ∷ x₃ ∷ xs) = (x₁ ⋈ x₂) ⋈ merges⁺ x₃ xs
\end{code}
%<*merges-sig>
\begin{code}
merges :  List (W × Forest A) →
          Link (Forest A)
\end{code}
%</merges-sig>
\begin{code}
merges [] = nothing
merges (x ∷ xs) = just (merges⁺ x xs)
\end{code}
%<*popMin>
\begin{code}
popMin : Forest A → List A × Link (Forest A)
popMin = map₂ merges ∘ swap ∘ partition out
\end{code}
%</popMin>
%<*search>
\begin{code}
search : Forest A → Chain (List A)
search = ana popMin
\end{code}
%</search>
