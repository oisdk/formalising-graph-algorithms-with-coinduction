\begin{code}
{-# OPTIONS --safe #-}

open import Algebra
open import Prelude
open import Path.Reasoning

module Data.Weighted.Monad {ℓ} {𝑆 : Type ℓ} (weight : Weight 𝑆) where

open Weight weight
open import Data.Weighted.Definition ⊕-semigroup
open import Data.Weighted.CommutativeMonoid ⊕-semigroup
open import Data.Weighted.Eliminators ⊕-semigroup
open import Data.Weighted.Condition ⊕-semigroup
open import Data.Weighted.Functor



module _ {A : Type a} {B : Type b} (f : A → B) where
  wmap-alg : A ⟶W B
  wmap-alg = record
    { act-w = λ w x → w ▹ f x ∷ ⟅⟆
    ; coh-w = λ p q x → dup p q (f x) ⟅⟆
    }

  wmap : Weighted A → Weighted B
  wmap = [ wmap-alg ]W↓

wmap-id : (xs : Weighted A) → wmap id xs ≡ xs
wmap-id = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ Weighted A ] ↦ (wmap id xs ≡ xs)
  alg .fst ⟅⟆ = refl
  alg .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (w ▹ x ∷_) P⟨xs⟩
  alg .snd = eq-coh

wmap-comp : (f : B → C) (g : A → B) (xs : Weighted A) → wmap f (wmap g xs) ≡ wmap (f ∘ g) xs
wmap-comp f g = ⟦ alg f g ⟧
  where
  alg : (f : B → C) (g : A → B) → Ψ[ xs ⦂ Weighted A ] ↦ wmap f (wmap g xs) ≡ wmap (f ∘ g) xs
  alg f g .fst ⟅⟆ = refl
  alg f g .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (w ▹ _ ∷_) P⟨xs⟩
  alg f g .snd = eq-coh

functorWeighted : Functor (Weighted {a = a})
functorWeighted .Functor.map = wmap
functorWeighted .Functor.map-id = wmap-id
functorWeighted .Functor.map-comp = wmap-comp

private module Display-⋊ where
  _∙_ = _⊗_

  infixr 5 _⋊_
  _⋊_ : 𝑆 → Weighted A → Weighted A
\end{code}
%<*rtimes>
\begin{code}[number=eqn:rtimes]
  w ⋊ ⟅⟆          = ⟅⟆
  w ⋊ p ▹ x ∷ xs  = w ∙ p ▹ x ∷ w ⋊ xs
\end{code}
%</rtimes>
\begin{code}

  w ⋊ com p x q y xs i = com (w ⊗ p) x (w ⊗ q) y (w ⋊ xs) i
  w ⋊ dup p q x xs i = (dup (w ⊗ p) (w ⊗ q) x (w ⋊ xs) ; cong (_▹ x ∷ w ⋊ xs) (sym (⊗⟨⊕⟩ w p q))) i
  w ⋊ trunc xs ys p q i j = trunc (w ⋊ xs) (w ⋊ ys) (cong (w ⋊_) p) (cong (w ⋊_) q) i j

⋊-alg : 𝑆 → A ⟶W A
⋊-alg w = cond-alg (w ⊗_) (λ p q → sym (⊗⟨⊕⟩ w p q))

infixr 5 _⋊_
_⋊_ : 𝑆 → Weighted A → Weighted A
w ⋊ xs = cond (w ⊗_) (λ p q → sym (⊗⟨⊕⟩ w p q)) xs

wmap-⋊ : ∀ w (f : A → B) xs → w ⋊ wmap f xs ≡ wmap f (w ⋊ xs)
wmap-⋊ w f = ⟦ alg w f ⟧
  where
  alg : ∀ w (f : A → B) → Ψ[ xs ⦂ Weighted A ] ↦ w ⋊ wmap f xs ≡ wmap f (w ⋊ xs)
  alg w f .snd = eq-coh
  alg w f .fst ⟅⟆ = refl
  alg w f .fst (p ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (w ⊗ p ▹ f x ∷_) P⟨xs⟩

⊕⟨⋊⟩ : ∀ p q (xs : Weighted A) → (p ⋊ xs) ∪ (q ⋊ xs) ≡ (p ⊕ q) ⋊ xs
⊕⟨⋊⟩ p q = ⟦ alg p q ⟧
  where
  alg : ∀ p q → Ψ[ xs ⦂ Weighted A ] ↦ ((p ⋊ xs) ∪ (q ⋊ xs) ≡ (p ⊕ q) ⋊ xs)
  alg p q .fst ⟅⟆ = refl
  alg p q .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
    (p ⋊ (w ▹ x ∷ xs)) ∪ (q ⋊ (w ▹ x ∷ xs)) ≡⟨⟩
    (p ⊗ w ▹ x ∷ p ⋊ xs) ∪ (q ⊗ w ▹ x ∷ q ⋊ xs) ≡⟨⟩
    p ⊗ w ▹ x ∷ (p ⋊ xs) ∪ (q ⊗ w ▹ x ∷ q ⋊ xs) ≡˘⟨ cong (p ⊗ w ▹ x ∷_) (∪-cons (q ⊗ w) x (p ⋊ xs) _) ⟩
    p ⊗ w ▹ x ∷ q ⊗ w ▹ x ∷ (p ⋊ xs) ∪ (q ⋊ xs) ≡⟨ dup (p ⊗ w) (q ⊗ w) x _ ⟩
    p ⊗ w ⊕ q ⊗ w ▹ x ∷ (p ⋊ xs) ∪ (q ⋊ xs) ≡⟨ cong₂ (_▹ x ∷_) (sym (⟨⊕⟩⊗ _ _ _)) P⟨xs⟩ ⟩
    (p ⊕ q) ⋊ (w ▹ x ∷ xs) ∎
  alg p q .snd = eq-coh

⋊⟨∪⟩ : ∀ w (x y : Weighted A) → w ⋊ (x ∪ y) ≡ (w ⋊ x) ∪ (w ⋊ y)
⋊⟨∪⟩ w x y = ⟦ alg w y ⟧ x
  where
  alg : ∀ w y → Ψ[ x ⦂ Weighted A ] ↦ (w ⋊ (x ∪ y) ≡ (w ⋊ x) ∪ (w ⋊ y))
  alg w y .snd = eq-coh
  alg w y .fst ⟅⟆ = refl
  alg w y .fst (u ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (w ⊗ u ▹ x ∷_) P⟨xs⟩

private module InlineBind where
  _>>=_ : Weighted A → (A → Weighted B) → Weighted B
\end{code}
%<*bind>
\begin{code}
  ⟅⟆            >>= k = ⟅⟆
  (p ▹ x ∷ xs)  >>= k = (p ⋊ k x) ∪ (xs >>= k)
\end{code}
%</bind>
\begin{code}
  com p x q y xs i >>= k = begin[ i ]
    (p ⋊ k x) ∪ (q ⋊ k y)   ∪ (xs >>= k) ≡˘⟨ ∪-assoc (p ⋊ k x) _ _ ⟩
    ((p ⋊ k x) ∪ (q ⋊ k y)) ∪ (xs >>= k) ≡⟨ cong (_∪ (xs >>= k)) (∪-com (p ⋊ k x) _) ⟩
    ((q ⋊ k y) ∪ (p ⋊ k x)) ∪ (xs >>= k) ≡⟨ ∪-assoc (q ⋊ k y) _ _ ⟩
    (q ⋊ k y) ∪ (p ⋊ k x)   ∪ (xs >>= k) ∎
  dup p q x xs i >>= k = begin[ i ]
    (p ⋊ k x) ∪ (q ⋊ k x) ∪ (xs >>= k) ≡˘⟨ ∪-assoc (p ⋊ k x) _ _ ⟩
    ((p ⋊ k x) ∪ (q ⋊ k x)) ∪ (xs >>= k) ≡⟨ cong (_∪ (xs >>= k)) (⊕⟨⋊⟩ p q (k x)) ⟩
    ((p ⊕ q) ⋊ k x) ∪ (xs >>= k) ∎
  trunc xs ys p q i j >>= k =
    trunc (xs >>= k) (ys >>= k) (cong (_>>= k) p) (cong (_>>= k) q) i j

module _ {A : Type a} {B : Type b} where
  bind-alg : (A → Weighted B) → A ⟶W B
  bind-alg k = record
    { act-w = λ w x → w ⋊ k x
    ; coh-w = λ p q x → ⊕⟨⋊⟩ p q (k x)
    }

  infixl 4.1 _>>=_
  _>>=_ : Weighted A → (A → Weighted B) → Weighted B
  xs >>= k = [ bind-alg k ]W↓ xs

  >>=-∪ : (xs ys : Weighted A) (k : A → Weighted B) → (xs ∪ ys) >>= k ≡ (xs >>= k) ∪ (ys >>= k)
  >>=-∪ xs ys k = collect-∪ (bind-alg k) xs ys

=<<-∪ : (xs : Weighted A) (ys zs : A → Weighted B) → (xs >>= λ x → ys x ∪ zs x) ≡ (xs >>= ys) ∪ (xs >>= zs)
=<<-∪ {B = B} xs ys zs = ⟦ alg ys zs ⟧ xs
  where
  lemma : (w x y z : Weighted B) → (w ∪ x) ∪ (y ∪ z) ≡ (w ∪ y) ∪ (x ∪ z)
  lemma w x y z =
    (w ∪ x) ∪ (y ∪ z) ≡⟨ ∪-assoc w x _ ; cong (w ∪_) (sym (∪-assoc x y z)) ⟩
    w ∪ (x ∪ y) ∪ z ≡⟨ cong (λ e → w ∪ e ∪ z) (∪-com x y ) ⟩
    w ∪ (y ∪ x) ∪ z ≡˘⟨ ∪-assoc w y _ ; cong (w ∪_) (sym (∪-assoc y x z)) ⟩
    (w ∪ y) ∪ (x ∪ z) ∎
    

  alg : (ys zs : A → Weighted B) → Ψ[ xs ⦂ Weighted A ] ↦ (xs >>= λ x → ys x ∪ zs x) ≡ (xs >>= ys) ∪ (xs >>= zs)
  alg ys zs .snd = eq-coh
  alg ys zs .fst ⟅⟆ = refl
  alg ys zs .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
    let k = λ x′ → ys x′ ∪ zs x′ in
    (w ▹ x ∷ xs) >>= k ≡⟨⟩
    (w ⋊ (ys x ∪ zs x)) ∪ (xs >>= k) ≡⟨ cong₂ _∪_ (⋊⟨∪⟩ w (ys x) (zs x)) P⟨xs⟩ ⟩ 
    ((w ⋊ ys x) ∪ (w ⋊ zs x)) ∪ ((xs >>= ys) ∪ (xs >>= zs))  ≡⟨ lemma (w ⋊ ys x) (w ⋊ zs x) (xs >>= ys) (xs >>= zs) ⟩
    ((w ⋊ ys x) ∪ (xs >>= ys)) ∪ ((w ⋊ zs x) ∪ (xs >>= zs)) ≡⟨⟩
    ((w ▹ x ∷ xs) >>= ys) ∪ ((w ▹ x ∷ xs) >>= zs) ∎


return : A → Weighted A
return x = 𝟙 ▹ x ∷ ⟅⟆

⋊-assoc : ∀ w v (s : Weighted A) → w ⋊ v ⋊ s ≡ (w ⊗ v) ⋊ s
⋊-assoc w v = ⟦ alg ⟧
  where
  alg : Ψ[ s ⦂ Weighted A ] ↦ w ⋊ v ⋊ s ≡ (w ⊗ v) ⋊ s
  alg .snd = eq-coh
  alg .fst ⟅⟆ = refl
  alg .fst (p ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong₂ (_▹ x ∷_) (sym (⊗-assoc w v p)) P⟨xs⟩

ε⋊ : (x : Weighted A) → 𝟙 ⋊ x ≡ x
ε⋊ = ⟦ alg ⟧
  where
  alg : Ψ[ s ⦂ Weighted A ] ↦ 𝟙 ⋊ s ≡ s
  alg .snd = eq-coh
  alg .fst ⟅⟆ = refl
  alg .fst (p ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong₂ (_▹ x ∷_) (𝟙⊗ p) P⟨xs⟩

⋊⟅⟆ : ∀ w (x : Weighted A) → w ⋊ x ≡ ⟅⟆ → x ≡ ⟅⟆
⋊⟅⟆ w = ⟦ alg ⟧
  where
  alg : Ψ[ x ⦂ Weighted A ] ↦ (w ⋊ x ≡ ⟅⟆ → x ≡ ⟅⟆)
  alg .fst ⟅⟆ _ = refl
  alg .fst (p ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) e = absurd (false≢true (cong null e))
  alg .snd = prop-coh λ _ → isProp→ (trunc _ _)

⋊->>= : ∀ p (xs : Weighted A) (k : A → Weighted B) → (p ⋊ xs) >>= k ≡ p ⋊ (xs >>= k)
⋊->>= p xs k = ⟦ alg p k ⟧ xs
  where
  alg : ∀ p (k : A → Weighted B) → Ψ[ xs ⦂ Weighted A ] ↦ (p ⋊ xs) >>= k ≡ p ⋊ (xs >>= k)
  alg p k .snd = eq-coh
  alg p k .fst ⟅⟆ = refl
  alg p k .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
    ((p ⊗ w) ▹ x ∷ (p ⋊ xs)) >>= k ≡⟨⟩
    ((p ⊗ w) ⋊ k x) ∪  ((p ⋊ xs) >>= k) ≡⟨ cong₂ _∪_ (sym (⋊-assoc p w (k x))) P⟨xs⟩ ⟩
    (p ⋊ (w ⋊ k x)) ∪ (p ⋊ (xs >>= k)) ≡˘⟨ ⋊⟨∪⟩ p (w ⋊ k x) (xs >>= k) ⟩
    p ⋊ ((w ⋊ k x) ∪ (xs >>= k)) ∎

>>=-assoc  : (xs : Weighted A) (ys : A → Weighted B) (zs : B → Weighted C)
           → (xs >>= ys) >>= zs ≡ xs >>= (λ x → ys x >>= zs)
>>=-assoc xs ys zs = ⟦ alg ys zs ⟧ xs
  where
  alg : (ys : A → Weighted B) (zs : B → Weighted C) →
        Ψ[ xs ⦂ Weighted A ] ↦ (xs >>= ys) >>= zs ≡ xs >>= (λ x → ys x >>= zs)
  alg ys zs .snd = eq-coh
  alg ys zs .fst ⟅⟆ = refl
  alg ys zs .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
    (w ▹ x ∷ xs) >>= ys >>= zs ≡⟨⟩
    ((w ⋊ ys x) ∪ (xs >>= ys)) >>= zs ≡⟨ >>=-∪ (w ⋊ ys x) (xs >>= ys) zs ⟩
    ((w ⋊ ys x) >>= zs) ∪ ((xs >>= ys) >>= zs) ≡⟨ cong₂ _∪_ (⋊->>= w (ys x) zs) P⟨xs⟩ ⟩
    (w ⋊ (ys x >>= zs)) ∪ (xs >>= (λ x → ys x >>= zs)) ≡⟨⟩
    (w ▹ x ∷ xs) >>= (λ x → ys x >>= zs) ∎

>>=-idˡ : (x : A) (k : A → Weighted B) → return x >>= k ≡ k x
>>=-idˡ x k = ∪-idʳ (𝟙 ⋊ k x) ; ε⋊ (k x)

>>=-idʳ : (xs : Weighted A) → xs >>= return ≡ xs
>>=-idʳ = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ Weighted A ] ↦ (xs >>= return) ≡ xs
  alg .snd = eq-coh
  alg .fst ⟅⟆ = refl
  alg .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong₂ (_▹ x ∷_) (⊗𝟙 w) P⟨xs⟩

module _ {A : Type a} {B : Type b} where
  >>=-⟅⟆ : (xs : Weighted A) → xs >>= const ⟅⟆ ≡ (⟅⟆ ⦂ Weighted B)
  >>=-⟅⟆ = ⟦ alg ⟧
    where
    alg : Ψ[ xs ⦂ Weighted A ] ↦ (xs >>= const ⟅⟆ ≡ (⟅⟆ ⦂ Weighted B))
    alg .snd = eq-coh
    alg .fst ⟅⟆ = refl
    alg .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = P⟨xs⟩

>>=-wmap : (f : A → B) (k : B → Weighted C) (xs : Weighted A) → wmap f xs >>= k ≡ xs >>= (k ∘ f)
>>=-wmap f k = ⟦ alg f k ⟧
  where
  alg : (f : A → B) (k : B → Weighted C) → Ψ[ xs ⦂ Weighted A ] ↦ wmap f xs >>= k ≡ xs >>= (k ∘ f)
  alg f k .snd = eq-coh
  alg f k .fst ⟅⟆ = refl
  alg f k .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong ((w ⋊ k (f x)) ∪_) P⟨xs⟩

wmap->>= : (f : A → B) (xs : Weighted A) → wmap f xs ≡ xs >>= (return ∘ f)
wmap->>= f = ⟦ alg f ⟧
  where
  alg : (f : A → B) → Ψ[ xs ⦂ Weighted A ] ↦ wmap f xs ≡ xs >>= (return ∘ f)
  alg f .snd = eq-coh
  alg f .fst ⟅⟆ = refl
  alg f .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong₂ _▹ f x ∷_ (sym (⊗𝟙 w)) P⟨xs⟩

\end{code}
