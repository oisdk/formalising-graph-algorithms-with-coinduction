{-# OPTIONS --lossy-unification --safe #-}

open import Algebra
open import Algebra.Monus
open import Prelude
open import Path.Reasoning

module Data.Weighted.CutoffMonus {ℓ} {𝑆 : Type ℓ} (mon : TMAPOM 𝑆) where

open TMAPOM mon

open import Data.Weighted.Definition ⊓-semigroup
open import Data.Weighted.CommutativeMonoid ⊓-semigroup
open import Data.Weighted.Monad (weight 𝑆 tapom)
open import Data.Weighted.Cutoff totalOrder
open import Data.Weighted.Eliminators ⊓-semigroup
open import Data.Weighted.Functor

⊢-wmap : ∀ (f : A → B) x w → wmap f x ⊢ w ≡ wmap f (x ⊢ w)
⊢-wmap f x w = ⟦ alg f w ⟧ x
  where
  alg : ∀ (f : A → B) w → Ψ[ x ⦂ Weighted A ] ↦ wmap f x ⊢ w ≡ wmap f (x ⊢ w)
  alg f w .snd = eq-coh
  alg f w .fst ⟅⟆ = refl
  alg f w .fst (q ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) with q ≤? w
  ... | yes _ = cong (q ▹ f x ∷_) P⟨xs⟩
  ... | no _ = P⟨xs⟩

>-⋊-⊢ : ∀ w (s : Weighted A) v → w > v → (w ⋊ s) ⊢ v ≡ ⟅⟆
>-⋊-⊢ w s v w>v = ⟦ alg w v w>v ⟧ s
  where
  alg : ∀ w v → w > v → Ψ[ s ⦂ Weighted A ] ↦ (w ⋊ s) ⊢ v ≡ ⟅⟆
  alg w v w>v .snd = eq-coh
  alg w v w>v .fst ⟅⟆ = refl
  alg w v w>v .fst (u ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
    (w ⋊ u ▹ x ∷ xs) ⊢ v         ≡⟨⟩
    (w ∙ u ▹ x ∷ w ⋊ xs) ⊢ v     ≡⟨⟩
    v / w ∙ u ▹ x ∪ (w ⋊ xs) ⊢ v ≡⟨ cong (_∪ (w ⋊ xs) ⊢ v) (/≰ v (w ∙ u) x ≲[ <[ w>v ] ≲; ≤[ x≤x∙y ] ]) ⟩
    (w ⋊ xs) ⊢ v ≡⟨ P⟨xs⟩ ⟩
    ⟅⟆ ∎

module Depth where
  Deeper : 𝑆 → Weighted A → Type-
  Deeper w x = ∃ y × w ⋊ y ≡ x

  deeper-≥ : ∀ v w (x : Weighted A) → Deeper v x → v ≥ w → Deeper w x
  deeper-≥ v w x (y , v>|x) (k , v≡w∙k) = k ⋊ y , (⋊-assoc w k y ; cong (_⋊ y) (sym v≡w∙k) ; v>|x)

  ε-deeper : (x : Weighted A) → Deeper ε x
  ε-deeper x = x , ε⋊ x

return-⊢ : ∀ (x : A) w → return x ⊢ w ≡ return x
return-⊢ x w = ∪-idʳ _ ; /≤ w ε x (positive w)

>>=-⊢-lemma : ∀ w v (x : A) (k : A → Weighted B) → (w ⋊ k x) ⊢ v ≡ (v / w ▹ x >>= k) ⊢ v
>>=-⊢-lemma w v x k with w ≤? v
... | no  w≰v = >-⋊-⊢ w (k x) v w≰v
... | yes w≤v = sym (cong (_⊢ v) (∪-idʳ (w ⋊ k x)))

>>=-⊢ˡ : ∀ v (s : Weighted A) (k : A → Weighted B) →
  (s >>= k) ⊢ v ≡ (s ⊢ v >>= k) ⊢ v
>>=-⊢ˡ v s k = ⟦ alg v k ⟧ s
  where
  alg : ∀ v (k : A → Weighted B) → Ψ[ s ⦂ Weighted A ] ↦ (s >>= k) ⊢ v ≡ (s ⊢ v >>= k) ⊢ v
  alg v k .snd = eq-coh
  alg v k .fst ⟅⟆ = refl
  alg v k .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
    (w ▹ x ∷ xs >>= k) ⊢ v                     ≡⟨⟩
    ((w ⋊ k x) ∪ (xs >>= k)) ⊢ v               ≡⟨ ⊢-∪ (w ⋊ k x) _ _ ⟩
    (w ⋊ k x) ⊢ v ∪ (xs >>= k) ⊢ v             ≡⟨ cong ((w ⋊ k x) ⊢ v ∪_) P⟨xs⟩ ⟩
    (w ⋊ k x) ⊢ v ∪ (xs ⊢ v >>= k) ⊢ v         ≡⟨ cong (_∪ (xs ⊢ v >>= k) ⊢ v) (>>=-⊢-lemma w v x k ) ⟩
    (v / w ▹ x >>= k) ⊢ v ∪ (xs ⊢ v >>= k) ⊢ v ≡˘⟨ ⊢-∪ (v / w ▹ x >>= k) _ _ ⟩
    ((v / w ▹ x >>= k) ∪ (xs ⊢ v >>= k)) ⊢ v   ≡˘⟨ cong (_⊢ v) (>>=-∪ (v / w ▹ x) _ k) ⟩
    (v / w ▹ x ∪ xs ⊢ v >>= k) ⊢ v             ≡⟨⟩
    ((w ▹ x ∷ xs) ⊢ v >>= k) ⊢ v ∎

/∙⊢ : ∀ u v w (x : A) → v / w ∙ u ▹ x ≡ (w ⋊ v / u ▹ x) ⊢ v
/∙⊢ u v w x with u ≤? v
... | yes _ = sym (∪-idʳ (v / w ∙ u ▹ x))
... | no u>v = /≰ v (w ∙ u) x ≲[ <[ u>v ] ≲; ≤[ x≤x∙y ] ≲; ≡[ comm u w ] ]

>>=-⊢ʳ-lemma : ∀ w (s : Weighted A) v → (w ⋊ s) ⊢ v ≡ (w ⋊ s ⊢ v) ⊢ v
>>=-⊢ʳ-lemma w s v = ⟦ alg w v ⟧ s
  where
  alg : ∀ w v → Ψ[ s ⦂ Weighted A ] ↦ (w ⋊ s) ⊢ v ≡ (w ⋊ s ⊢ v) ⊢ v
  alg w v .snd = eq-coh
  alg w v .fst ⟅⟆ = refl
  alg w v .fst (u ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
    (w ⋊ u ▹ x ∷ xs) ⊢ v                   ≡⟨⟩
    (w ∙ u ▹ x ∷ w ⋊ xs) ⊢ v               ≡⟨⟩
    v / w ∙ u ▹ x ∪ (w ⋊ xs) ⊢ v           ≡⟨ cong (v / w ∙ u ▹ x ∪_) P⟨xs⟩ ⟩
    v / w ∙ u ▹ x ∪ (w ⋊ xs ⊢ v) ⊢ v       ≡⟨ cong (_∪ (w ⋊ xs ⊢ v) ⊢ v) (/∙⊢ u v w x) ⟩
    (w ⋊ v / u ▹ x) ⊢ v ∪ (w ⋊ xs ⊢ v) ⊢ v ≡˘⟨ ⊢-∪ (w ⋊ v / u ▹ x) _ v ⟩
    ((w ⋊ v / u ▹ x) ∪ (w ⋊ xs ⊢ v)) ⊢ v   ≡˘⟨ cong (_⊢ v) (⋊⟨∪⟩ w (v / u ▹ x) _) ⟩
    (w ⋊ v / u ▹ x ∪ xs ⊢ v) ⊢ v           ≡⟨⟩
    (w ⋊ (u ▹ x ∷ xs) ⊢ v) ⊢ v ∎

>>=-⊢ʳ : ∀ v (s : Weighted A) (k : A → Weighted B) →
  (s >>= k) ⊢ v ≡ (s >>= k ∘⊢ v) ⊢ v
>>=-⊢ʳ v s k = ⟦ alg v k ⟧ s
  where
  alg : ∀ v (k : A → Weighted B) → Ψ[ s ⦂ Weighted A ] ↦ (s >>= k) ⊢ v ≡ (s >>= k ∘⊢ v) ⊢ v
  alg v k .snd = eq-coh
  alg v k .fst ⟅⟆ = refl
  alg v k .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
    (w ▹ x ∷ xs >>= k) ⊢ v                  ≡⟨⟩
    ((w ⋊ k x) ∪ (xs >>= k)) ⊢ v            ≡⟨ ⊢-∪ (w ⋊ k x) _ _ ⟩
    (w ⋊ k x) ⊢ v ∪ (xs >>= k) ⊢ v          ≡⟨ cong ((w ⋊ k x) ⊢ v ∪_) P⟨xs⟩ ⟩
    (w ⋊ k x) ⊢ v ∪ (xs >>= k ∘⊢ v) ⊢ v     ≡⟨ cong (_∪ (xs >>= k ∘⊢ v) ⊢ v) (>>=-⊢ʳ-lemma w (k x) v) ⟩
    (w ⋊ k x ⊢ v) ⊢ v ∪ (xs >>= k ∘⊢ v) ⊢ v ≡˘⟨ ⊢-∪ (w ⋊ k x ⊢ v) _ _ ⟩
    ((w ⋊ k x ⊢ v) ∪ (xs >>= k ∘⊢ v)) ⊢ v   ≡⟨⟩
    (w ▹ x ∷ xs >>= k ∘⊢ v) ⊢ v ∎

module _ {A : Type a} where
  ⋊-∪-⋊ : ∀ (x y : Weighted A) p q → p ≤ q → y ⊑ x → q ⋊ y ⊆ p ⋊ x
  ⋊-∪-⋊ x y p q p≤q (k , y⊑x) = ∪-com (q ⋊ y) (p ⋊ x) ; cong (λ e → (p ⋊ x) ∪ (q ⋊ e)) y⊑x ; ⟦ alg ⟧ x
    where
    alg : Ψ[ x ⦂ Weighted A ] ↦ (p ⋊ x) ∪ (q ⋊ x ⊢ k) ≡ p ⋊ x
    alg .fst ⟅⟆ = refl
    alg .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) with w ≤? k
    ... | yes w≤k =
      (p ⋊ w ▹ x ∷ xs) ∪ (q ⋊ w ▹ x ∷ (xs ⊢ k))            ≡⟨⟩
      (p ∙ w ▹ x ∷ p ⋊ xs) ∪ (q ∙ w ▹ x ∷ q ⋊ (xs ⊢ k))    ≡˘⟨ cong (p ∙ w ▹ x ∷_) (∪-cons (q ∙ w) x _ _) ⟩
      p ∙ w ▹ x ∷ q ∙ w ▹ x ∷ (p ⋊ xs) ∪ (q ⋊ xs ⊢ k)      ≡⟨ dup (p ∙ w) (q ∙ w) x _ ⟩
      ((p ∙ w) ⊓ (q ∙ w)) ▹ x ∷ (p ⋊ xs) ∪ (q ⋊ (xs ⊢ k))  ≡⟨ cong (_▹ x ∷ ((p ⋊ xs) ∪ (q ⋊ xs ⊢ k))) (⊓≤≡ (p ∙ w) (q ∙ w) (≤-congʳ w p≤q)) ⟩
      (p ∙ w) ▹ x ∷ (p ⋊ xs) ∪ (q ⋊ (xs ⊢ k))              ≡⟨ cong (p ∙ w ▹ x ∷_) P⟨xs⟩ ⟩
      (p ∙ w) ▹ x ∷ (p ⋊ xs)                                ≡⟨⟩
      p ⋊ w ▹ x ∷ xs ∎
    ... | no  w≰k =
      (p ⋊ w ▹ x ∷ xs) ∪ (q ⋊ (xs ⊢ k))     ≡⟨⟩
      p ∙ w ▹ x ∷ (p ⋊ xs) ∪ (q ⋊ (xs ⊢ k)) ≡⟨ cong (p ∙ w ▹ x ∷_) P⟨xs⟩ ⟩
      p ∙ w ▹ x ∷ (p ⋊ xs)                   ≡⟨⟩
      p ⋊ w ▹ x ∷ xs ∎
    alg .snd = eq-coh


