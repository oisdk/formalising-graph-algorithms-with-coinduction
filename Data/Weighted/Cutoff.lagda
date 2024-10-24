\begin{code}
{-# OPTIONS --safe #-}

open import Algebra
open import Prelude hiding ([_])
open import Relation.Binary

module Data.Weighted.Cutoff {ℓ₁ ℓ₂ ℓ₃} {W : Type ℓ₁} (ord : TotalOrder W ℓ₂ ℓ₃) where

open TotalOrder ord hiding (refl)

open import Data.Weighted.Definition ⊓-semigroup
open import Data.Weighted.Eliminators ⊓-semigroup
open import Data.Weighted.CommutativeMonoid ⊓-semigroup
open import Data.Weighted.Functor



open import Path.Reasoning

module _ {A : Type a} where
  _/_▹_ : W → W → A → Weighted A
  c / p ▹ x = if p ≤ᵇ c then p ▹ x ∷ ⟅⟆ else ⟅⟆

  _//_▹_ : W → W → A → Weighted A
  c // p ▹ x = if p <ᵇ c then p ▹ x ∷ ⟅⟆ else ⟅⟆

  _⊣-alg : W → A ⟶W A
  (w ⊣-alg) .act-w p x = w / p ▹ x
  (w ⊣-alg) .coh-w p q x with p ≤? w | q ≤? w | p ⊓ q ≤? w
  ... | no  p≰w | no  q≰w | no  p⊓q≰w = refl
  ... | yes p≤w | yes q≤w | yes p⊓q≤w = dup p q x ⟅⟆
  ... | yes p≤w | no  q≰w | yes p⊓q≤w = cong (_▹ x ∷ ⟅⟆) (sym (⊓≤≡ p q ≲[ ≤[ p≤w ] ≲; ≤[ <⇒≤ (≰⇒> q≰w) ] ]))
  ... | no  p≰w | yes q≤w | yes p⊓q≤w = cong (_▹ x ∷ ⟅⟆) (sym (⊓≤≡ q p ≲[ ≤[ q≤w ] ≲; ≤[ <⇒≤ (≰⇒> p≰w) ] ] ) ; ⊓-comm q p)
  ... | yes p≤w | _       | no  p⊓q≰w = absurd (p⊓q≰w ≲[ ≤[ ⊓≤ p q ] ≲; ≤[ p≤w ] ])
  ... | _       | yes q≤w | no  p⊓q≰w = absurd (p⊓q≰w ≲[ ≡[ ⊓-comm p q ] ≲; ≤[ ⊓≤ q p ] ≲; ≤[ q≤w ] ])
  ... | no  p≰w | no  q≰w | yes p⊓q≤w with p <? q
  ... | yes _ = absurd (p≰w p⊓q≤w)
  ... | no  _ = absurd (q≰w p⊓q≤w)

  cutoff-lt-alg : W → Ψ[ xs ⦂ Weighted A ] ↦ Weighted A
  cutoff-lt-alg w .fst ⟅⟆ = ⟅⟆
  cutoff-lt-alg w .fst (p ▹ x ∷ _ ⟨ xs ⟩) = w // p ▹ x ∪ xs
  cutoff-lt-alg w .snd .c-set _ = trunc
  cutoff-lt-alg w .snd .c-com p x q y _ xs =
        w // p ▹ x ∪ w // q ▹ y ∪ xs   ≡˘⟨ ∪-assoc (w // p ▹ x) _ _ ⟩
        (w // p ▹ x ∪ w // q ▹ y) ∪ xs ≡⟨ cong (_∪ xs) ( ∪-com (w // p ▹ x) _) ⟩
        (w // q ▹ y ∪ w // p ▹ x) ∪ xs ≡⟨ ∪-assoc (w // q ▹ y) _ _ ⟩
        w // q ▹ y ∪ w // p ▹ x ∪ xs ∎

  cutoff-lt-alg w .snd .c-dup p q x _ xs with p <? w | q <? w | p ⊓ q <? w
  ... | no  p≮w | no  q≮w | no  p⊓q≮w = refl
  ... | yes p<w | yes q<w | yes p⊓q<w = dup p q x xs
  ... | yes p<w | no  q≮w | yes p⊓q<w = cong (_▹ x ∷ xs) (sym (⊓≤≡ p q (<⇒≤ ≲[ <[ p<w ] ≲; ≤[ ≮⇒≥ q≮w ] ])))
  ... | no  p≮w | yes q<w | yes p⊓q<w = cong (_▹ x ∷ xs) (sym (⊓≤≡ q p (<⇒≤ ≲[ <[ q<w ] ≲; ≤[ ≮⇒≥ p≮w ] ]) ) ; ⊓-comm q p)
  ... | yes p<w | _       | no  p⊓q≮w = absurd (p⊓q≮w ≲[ ≤[ ⊓≤ p q ] ≲; <[ p<w ] ])
  ... | _       | yes q<w | no  p⊓q≮w = absurd (p⊓q≮w ≲[ ≡[ ⊓-comm p q ] ≲; ≤[ ⊓≤ q p ] ≲; <[ q<w ] ])
  ... | no  p≮w | no  q≮w | yes p⊓q<w with p <? q
  ... | yes _ = absurd (p≮w p⊓q<w)
  ... | no  _ = absurd (q≮w p⊓q<w)

  infixl 6 _⊢_
  _⊢_ : Weighted A → W → Weighted A
  x ⊢ w = [ w ⊣-alg ]W↓ x

  infixl 6 _⊨_
  _⊨_ : Weighted A → W → Weighted A
  x ⊨ w = ⟦ cutoff-lt-alg w ⟧ x
  ⊢-≥ : ∀ s v w → v ≥ w → s ⊢ v ⊢ w ≡ s ⊢ w
  ⊢-≥ s v w v≥w = ⟦ cutoff-≤-alg ⟧ s
    where
    cutoff-≤-alg : Ψ[ s ⦂ Weighted A ] ↦ s ⊢ v ⊢ w ≡ s ⊢ w
    cutoff-≤-alg .fst ⟅⟆ = refl
    cutoff-≤-alg .fst (p ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) with p ≤? v
    cutoff-≤-alg .fst (p ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) | no  p≰v with p ≤? w
    cutoff-≤-alg .fst (p ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) | no p≰v | yes p≤w = absurd (p≰v (≤-trans p≤w v≥w))
    cutoff-≤-alg .fst (p ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) | no p≰v | no  p≰w = P⟨xs⟩
    cutoff-≤-alg .fst (p ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) | yes p≤v with p ≤? w
    cutoff-≤-alg .fst (p ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) | yes p≤v | yes p≤w = cong (p ▹ x ∷_) P⟨xs⟩
    cutoff-≤-alg .fst (p ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) | yes p≤v | no  p≰w = P⟨xs⟩
    cutoff-≤-alg .snd = prop-coh λ _ → trunc _ _ 

  ⊢-ε : ∀ w → ⟅⟆ ⊢ w ≡ ⟅⟆
  ⊢-ε w = refl

  ⊢-∪ : ∀ s t w → (s ∪ t) ⊢ w ≡ s ⊢ w ∪ t ⊢ w
  ⊢-∪ xs ys w = collect-∪ (w ⊣-alg) xs ys 

  /≤ : ∀ w p x → p ≤ w → w / p ▹ x ≡ p ▹ x ∷ ⟅⟆
  /≤ w p x p≤w with p ≤? w
  ... | yes _ = refl
  ... | no p≰w = absurd (p≰w p≤w)

  /≰ : ∀ w p x → p ≰ w → w / p ▹ x ≡ ⟅⟆
  /≰ w p x p≰w with p ≤? w
  ... | yes p≤w = absurd (p≰w p≤w)
  ... | no _ = refl

  /▹-comm : ∀ w₁ w₂ p x → (w₁ / p ▹ x) ⊢ w₂ ≡ (w₂ / p ▹ x) ⊢ w₁
  /▹-comm w₁ w₂ p x with p ≤? w₁ | p ≤? w₂
  ... | yes p≤w₁ | yes p≤w₂ = cong (_∪ ⟅⟆) (/≤ w₂ p x p≤w₂ ; sym (/≤ w₁ p x p≤w₁))
  ... | no  p≰w₁ | no  p≰w₂ = refl
  ... | no  p≰w₁ | yes p≤w₂ = sym (cong (_∪ ⟅⟆) (/≰ w₁ p x p≰w₁))
  ... | yes p≤w₁ | no  p≰w₂ = cong (_∪ ⟅⟆) (/≰ w₂ p x p≰w₂)

  ⊢-com : ∀ s v w → s ⊢ v ⊢ w ≡ s ⊢ w ⊢ v
  ⊢-com s w₁ w₂ = ⟦ alg ⟧ s
    where
    alg : Ψ[ s ⦂ Weighted A ] ↦ s ⊢ w₁ ⊢ w₂ ≡ s ⊢ w₂ ⊢ w₁
    alg .fst (p ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
      (p ▹ x ∷ xs) ⊢ w₁ ⊢ w₂         ≡⟨⟩
      (w₁ / p ▹ x ∪ xs ⊢ w₁) ⊢ w₂    ≡⟨ ⊢-∪ (w₁ / p ▹ x) _ _ ⟩
      w₁ / p ▹ x ⊢ w₂ ∪ xs ⊢ w₁ ⊢ w₂ ≡⟨ cong₂ _∪_ (/▹-comm w₁ w₂ p x) P⟨xs⟩ ⟩
      w₂ / p ▹ x ⊢ w₁ ∪ xs ⊢ w₂ ⊢ w₁ ≡˘⟨ ⊢-∪ (w₂ / p ▹ x) _ _ ⟩
      (p ▹ x ∷ xs) ⊢ w₂ ⊢ w₁ ∎
    alg .fst ⟅⟆ = refl
    alg .snd = eq-coh

  ⊢-⊓ :
\end{code}
%<*cutoff-min>
\begin{code}[number=code:cutoff-min]
    ∀ s v w → (s ⊢ v) ⊢ w ≡ s ⊢ (v ⊓ w)
\end{code}
%</cutoff-min>
\begin{code}
  ⊢-⊓ s v w with v <? w
  ... | no  v≮w = ⊢-≥ s v w (≮⇒≥ v≮w)
  ... | yes v<w = ⊢-com s v w ; ⊢-≥ s w v (<⇒≤ v<w)

infixl 6 _∘⊢_
_∘⊢_ : (A → Weighted B) → W → A → Weighted B
(k ∘⊢ w) x = k x ⊢ w

infix 4 _⊑_
_⊑_ : Weighted A → Weighted A → Type-
xs ⊑ ys = ∃ k × xs ≡ ys ⊢ k

⊑-antisym : {x y : Weighted A} → x ⊑ y → y ⊑ x → x ≡ y
⊑-antisym {x = x} {y} (k₁ , x≡y⊢k₁) (k₂ , y≡x⊢k₂) with k₁ ≤|≥ k₂ 
... | inl k₁≤k₂ = x≡y⊢k₁ ; sym (⊢-≥ y _ _ k₁≤k₂) ; ⊢-com y k₂ k₁ ; sym (cong (_⊢ k₂) x≡y⊢k₁) ; sym y≡x⊢k₂
... | inr k₂≤k₁ = x≡y⊢k₁ ; cong (_⊢ k₁) y≡x⊢k₂ ; ⊢-com x k₂ k₁ ; ⊢-≥ x _ _ k₂≤k₁ ; sym y≡x⊢k₂

⊢-∪-idem : ∀ k (x : Weighted A) → x ∪ x ⊢ k ≡ x
⊢-∪-idem k = ⟦ alg k ⟧
  where
  alg : ∀ k → Ψ[ x ⦂ Weighted A ] ↦ x ∪ x ⊢ k ≡ x
  alg k .fst ⟅⟆ = refl
  alg k .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) with w ≤? k
  ... | yes w≤k =
    w ▹ x ∷ xs ∪ w ▹ x ∷ xs ⊢ k ≡˘⟨ cong (w ▹ x ∷_) (∪-cons w x xs (xs ⊢ k)) ⟩
    w ▹ x ∷ w ▹ x ∷ xs ∪ xs ⊢ k ≡⟨ dup w w x (xs ∪ xs ⊢ k) ⟩
    w ⊓ w ▹ x ∷ xs ∪ xs ⊢ k ≡⟨ cong (_▹ x ∷ xs ∪ xs ⊢ k) (⊓-idem w) ⟩
    w ▹ x ∷ xs ∪ xs ⊢ k ≡⟨ cong (w ▹ x ∷_) P⟨xs⟩ ⟩
    w ▹ x ∷ xs ∎
  ... | no  _ = cong (w ▹ x ∷_) P⟨xs⟩
  alg k .snd = eq-coh

⊑-∪ : (x y : Weighted A) → x ⊑ y → x ∪ y ≡ y
⊑-∪ x y (k , x⊑y) = cong (_∪ y) x⊑y ; ∪-com (y ⊢ k) y ; ⊢-∪-idem k y
\end{code}
