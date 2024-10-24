\begin{code}
{-# OPTIONS --safe #-}

open import Algebra.Monus
open import Prelude
open import Algebra

module Data.Weighted.Free  {S : Type}  (mon : TMAPOM S) where

open TMAPOM mon

open import Data.Weighted.Definition ⊓-semigroup
open import Data.Weighted.Eliminators ⊓-semigroup
open import Data.Weighted.CommutativeMonoid ⊓-semigroup
  using ()
  renaming
    ( _∪_ to _∪′_
    )
open import Data.Weighted.Monad (weight S tapom) renaming (_⋊_ to _⋊′_) hiding (⋊⟨∪⟩)
open import Data.Weighted.Functor

open import Path.Reasoning

S-weight : Weight S
S-weight = weight S tapom

𝒲 : Type → Type _
\end{code}
%<*church>
\begin{code}
𝒲 A = ∀ (V : Type) → isSet V → (mod : WeightSemimodule S-weight V) → (A → V) → V
\end{code}
%</church>
\begin{code}

η : A → Weighted A
η = return

wng : Weight S
wng = weight S tapom

open import Data.Weighted.Semimodule mon

module _ {ℓ̬} {V : Type ℓ̬} (isSetV : isSet V) (mod : WeightSemimodule wng V) where
  open WeightSemimodule mod
  
  module _ (f : A → V) where
    ⟦f⟧ : Weighted A → V
    ⟦f⟧ = ⟦ alg ⟧
      where
      alg : Ψ[ xs ⦂ Weighted A ] ↦ V
      alg .fst ⟅⟆ = ∅
      alg .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = (w ⋊ f x) ∪ P⟨xs⟩
      alg .snd .c-set _ = isSetV
      alg .snd .c-dup p q x xs ψ⟨xs⟩ =
        p ⋊ f x ∪ (q ⋊ f x ∪ ψ⟨xs⟩) ≡˘⟨ ∪-assoc (p ⋊ f x) (q ⋊ f x) ψ⟨xs⟩ ⟩
        (p ⋊ f x ∪ q ⋊ f x) ∪ ψ⟨xs⟩ ≡˘⟨ cong (_∪ ψ⟨xs⟩) (⟨+⟩⋊ p q (f x)) ⟩
        p ⊓ q ⋊ f x ∪ ψ⟨xs⟩ ∎

      alg .snd .c-com p x q y xs ψ⟨xs⟩ =
        p ⋊ f x ∪ (q ⋊ f y ∪ ψ⟨xs⟩) ≡˘⟨ ∪-assoc _ _ _ ⟩
        (p ⋊ f x ∪ q ⋊ f y) ∪ ψ⟨xs⟩ ≡⟨ cong (_∪ ψ⟨xs⟩) ( ∪-com (p ⋊ f x) (q ⋊ f y)) ⟩
        (q ⋊ f y ∪ p ⋊ f x) ∪ ψ⟨xs⟩ ≡⟨ ∪-assoc _ _ _ ⟩
        q ⋊ f y ∪ (p ⋊ f x ∪ ψ⟨xs⟩) ∎

    ⟦f⟧-⋊-hom : ∀ p x → ⟦f⟧ (p ⋊′ x) ≡ p ⋊ ⟦f⟧ x
    ⟦f⟧-⋊-hom p = ⟦ alg p ⟧
      where
      alg : ∀ p → Ψ[ x ⦂ Weighted A ] ↦ ⟦f⟧ (p ⋊′ x) ≡ p ⋊ ⟦f⟧ x
      alg p .snd = prop-coh λ _ → isSetV _ _
      alg p .fst ⟅⟆ = sym (⋊∅ _)
      alg p .fst (q ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
        ⟦f⟧ (p ⋊′ (q ▹ x ∷ xs)) ≡⟨⟩
        ⟦f⟧ (p ⊗ q ▹ x ∷ (p ⋊′ xs)) ≡⟨⟩
        ((p ⊗ q) ⋊ f x) ∪ ⟦f⟧ (p ⋊′ xs) ≡⟨ cong₂ _∪_ (⟨*⟩⋊ p q (f x)) P⟨xs⟩ ⟩
        (p ⋊ q ⋊ f x) ∪ (p ⋊ ⟦f⟧ xs) ≡˘⟨ ⋊⟨∪⟩ p _ _ ⟩
        p ⋊ (q ⋊ f x ∪ ⟦f⟧ xs) ≡⟨⟩
        p ⋊ ⟦f⟧ (q ▹ x ∷ xs) ∎

    ⟦f⟧-∙-hom : ∀ x y → ⟦f⟧ (x ∪′ y) ≡ ⟦f⟧ x ∪ ⟦f⟧ y
    ⟦f⟧-∙-hom x y = ⟦ alg y ⟧ x
      where
      alg : ∀ y → Ψ[ x ⦂ Weighted A ] ↦ ⟦f⟧ (x ∪′ y) ≡ ⟦f⟧ x ∪ ⟦f⟧ y
      alg ys .snd = prop-coh λ _ → isSetV _ _
      alg ys .fst ⟅⟆ = sym (∅∪ _)
      alg ys .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
        ⟦f⟧ (w ▹ x ∷ xs ∪′ ys) ≡⟨⟩
        (w ⋊ f x) ∪ ⟦f⟧ (xs ∪′ ys) ≡⟨ cong ((w ⋊ f x) ∪_) P⟨xs⟩ ⟩
        (w ⋊ f x) ∪ (⟦f⟧ xs ∪ ⟦f⟧ ys) ≡˘⟨ ∪-assoc (w ⋊ f x) (⟦f⟧ xs) (⟦f⟧ ys) ⟩
        ((w ⋊ f x) ∪ ⟦f⟧ xs) ∪ ⟦f⟧ ys ≡⟨⟩
        ⟦f⟧ (w ▹ x ∷ xs) ∪ ⟦f⟧ ys ∎

    hom : WeightHomomorphism[ wng ] weightedSemimodule {A = A} ⟶ mod
    hom .WeightHomomorphism[_]_⟶_.mon-homo .MonoidHomomorphism_⟶_.f = ⟦f⟧
    hom .WeightHomomorphism[_]_⟶_.mon-homo .MonoidHomomorphism_⟶_.∙-homo = ⟦f⟧-∙-hom
    hom .WeightHomomorphism[_]_⟶_.mon-homo .MonoidHomomorphism_⟶_.ε-homo = refl
    hom .WeightHomomorphism[_]_⟶_.⋊-homo = ⟦f⟧-⋊-hom

    module _ (hom′ : WeightHomomorphism[ wng ] weightedSemimodule { A = A } ⟶ mod)
             (diag : ∀ x → WeightHomomorphism[_]_⟶_.f hom′ (return x) ≡ f x) where
      open WeightHomomorphism[_]_⟶_ hom′
        renaming (f to h)

      uniq : ∀ x → h x ≡ ⟦f⟧ x
      uniq = ⟦ alg ⟧
        where
        alg : Ψ[ xs ⦂ Weighted A ] ↦ h xs ≡ ⟦f⟧ xs
        alg .snd = prop-coh λ _ → isSetV _ _
        alg .fst ⟅⟆ = ε-homo
        alg .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
          h (w ▹ x ∷ xs) ≡⟨⟩
          h ((w ▹ x ∷ ⟅⟆) ∪′ xs) ≡⟨ ∙-homo (w ▹ x ∷ ⟅⟆) xs ⟩
          h (w ▹ x ∷ ⟅⟆) ∪ h xs ≡˘⟨ cong (λ e → h (e ▹ x ∷ ⟅⟆) ∪ h xs) (⊗𝟙 w) ⟩
          h (w ⊗ 𝟙 ▹ x ∷ ⟅⟆) ∪ h xs ≡⟨⟩
          h (w ⋊′ η x) ∪ h xs ≡⟨ cong₂ _∪_ (⋊-homo w (η x) ; cong (w ⋊_) (diag x)) P⟨xs⟩ ⟩
          w ⋊ f x ∪ ⟦f⟧ xs ≡⟨⟩
          ⟦f⟧ (w ▹ x ∷ xs) ∎

module _ {A : Type} where
  𝒲-surj : 𝒲 A ↠! Weighted A
  𝒲-surj .fst w = w (Weighted A) trunc weightedSemimodule return
  𝒲-surj .snd xs .image _ set mod f = ⟦f⟧ set mod f xs
  𝒲-surj .snd xs .reflects = ⟦ alg ⟧ xs
    where
    alg : Ψ[ xs ⦂ Weighted A ] ↦ ⟦f⟧ trunc weightedSemimodule return xs ≡ xs
    alg .snd = eq-coh
    alg .fst ⟅⟆ = refl
    alg .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong₂ _▹ x ∷_ (∙ε w) P⟨xs⟩
\end{code}
