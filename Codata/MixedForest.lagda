\begin{code}
{-# OPTIONS --safe --termination-depth=10 #-}

open import Prelude
open import Algebra
open import Algebra.Monus

module Codata.MixedForest {W : Type} (mon : StrictWellFoundedMonus W) where

open StrictWellFoundedMonus mon

open Weight (weight W tapom)

open import Data.Weighted ⊕-semigroup hiding (⟪_⟫)
open import Data.Weighted.Monad (weight W tapom) hiding (_>>=_; return)
import Data.Weighted.Monad (weight _ tapom) as WB

open import Codata.Chain W

mutual
  data Forest∞ (A : Type) : Type where
    _#_ : W → Forest A → Forest∞ A
    ⟪_⟫ : Forest♭ A → Forest∞ A
    ! : A → Forest∞ A

  record Forest♭ (A : Type) : Type where
    coinductive
    field
      size : W
      deep : size ≢ ε
      next : Forest A

  Forest : Type → Type
  Forest A = List (Forest∞ A)
open Forest♭ public

mutual
  depth  : ∀ w → Acc _≺_ w → Forest A → Weighted A
  depth w wf [] = ⟅⟆
  depth w wf (f ∷ fs) = step′ w wf f ∪ depth w wf fs

  step′  : ∀ w → Acc _≺_ w → Forest∞ A → Weighted A
  step′ w wf (! x) = WB.return x

  step′ w wf (v # xs) with v ≟ ε | v ≤? w
  ... | yes v≡ε | _ = depth w wf xs
  ... | _ | no _ = ⟅⟆
  step′ w (acc wf) (v # xs) | no v≢ε | yes (k , w≡v∙k) =
    depth k (wf k (v , (w≡v∙k ; comm v k) , v≢ε)) xs

  step′ w wf ⟪ xs ⟫ with size xs ≤? w
  ... | no _ = ⟅⟆
  step′ w (acc wf) ⟪ xs ⟫ | yes (k , w≡v∙k) =
    depth k (wf k (size xs , (w≡v∙k ; comm _ k) , deep xs)) (xs .next)

_⊢_ : Forest A → W → Weighted A
xs ⊢ w = depth w (well-founded w) xs

_⋈_ :  W × Forest A → W × Forest A →
       W × Forest A
(wₗ , ls) ⋈ (wᵣ , rs) with wₗ ≤|≥ wᵣ
... | inl  (wᵣ∸wₗ  , _) = wₗ  , wᵣ∸wₗ # rs ∷ ls
... | inr  (wₗ∸wᵣ  , _) = wᵣ  , wₗ∸wᵣ # ls ∷ rs

merges⁺ : W × Forest A → List (W × Forest A) → W × Forest A
merges⁺ x₁ [] = x₁
merges⁺ x₁ (x₂ ∷ []) = x₁ ⋈ x₂
merges⁺ x₁ (x₂ ∷ x₃ ∷ xs) = (x₁ ⋈ x₂) ⋈ merges⁺ x₃ xs

open import Data.Link W

merges :  List (W × Forest A) →
          Link (Forest A)
merges [] = nothing
merges (x ∷ xs) = just (merges⁺ x xs)

-- popMin : Forest A → List A × Link (Forest A)
-- popMin = map₂ merges ∘ swap ∘ partition {!!}
\end{code}
