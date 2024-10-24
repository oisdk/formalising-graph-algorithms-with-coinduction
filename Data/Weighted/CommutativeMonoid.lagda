\begin{code}
{-# OPTIONS --safe #-}

open import Algebra
open import Prelude
open import Path.Reasoning

module Data.Weighted.CommutativeMonoid {ℓ} {𝑆 : Type ℓ} (sgp : Semigroup 𝑆) where

open import Data.Weighted.Definition sgp
open import Data.Weighted.Eliminators sgp
open import Data.Weighted.Functor

open Semigroup sgp
module _ {A : Type a} where
  infixr 5 _∪_
  _∪_ :  Weighted A → Weighted A → Weighted A
  ⟅⟆            ∪ ys = ys
  (p ▹ x ∷ xs)  ∪ ys = p ▹ x ∷ xs ∪ ys
  com p x q y xs i ∪ ys = com p x q y (xs ∪ ys) i
  dup p q x xs i ∪ ys = dup p q x (xs ∪ ys) i
  trunc xs₁ xs₂ p q i j ∪ ys =
    trunc (xs₁ ∪ ys) (xs₂ ∪ ys) (cong (_∪ ys) p) (cong (_∪ ys) q) i j

  ∪-assoc : Associative _∪_
  ∪-assoc xs ys zs = ⟦ ∪-assoc-alg ys zs ⟧ xs
    where
    ∪-assoc-alg : ∀ ys zs → Ψ[ xs ⦂ Weighted A ] ↦ ((xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs))
    ∪-assoc-alg ys zs .fst ⟅⟆ = refl
    ∪-assoc-alg ys zs .fst (w ▹ x ∷ _ ⟨ P⟨xs⟩ ⟩) = cong (w ▹ x ∷_) P⟨xs⟩
    ∪-assoc-alg ys zs .snd = eq-coh

  ∪-cons : ∀ w x xs ys → w ▹ x ∷ xs ∪ ys ≡ xs ∪ w ▹ x ∷ ys
  ∪-cons w x xs ys = ⟦ ∪-cons-alg w x ys ⟧ xs
    where
    ∪-cons-alg : ∀ w x ys → Ψ[ xs ⦂ Weighted A ] ↦ (w ▹ x ∷ xs ∪ ys ≡ xs ∪ w ▹ x ∷ ys)
    ∪-cons-alg w x ys .snd = eq-coh
    ∪-cons-alg w x ys .fst ⟅⟆ = refl
    ∪-cons-alg p x ys .fst (q ▹ y ∷ xs ⟨ P⟨xs⟩ ⟩) =
      p ▹ x ∷ q ▹ y ∷ xs ∪ ys ≡⟨ com p x q y _ ⟩
      q ▹ y ∷ p ▹ x ∷ xs ∪ ys ≡⟨ cong (q ▹ y ∷_) P⟨xs⟩ ⟩
      q ▹ y ∷ xs ∪ p ▹ x ∷ ys ∎

  ∪-idʳ : ∀ xs → xs ∪ ⟅⟆ ≡ xs
  ∪-idʳ = ⟦ ∪-idʳ-alg ⟧
    where
    ∪-idʳ-alg : Ψ[ xs ⦂ Weighted A ] ↦ (xs ∪ ⟅⟆ ≡ xs)
    ∪-idʳ-alg .snd = eq-coh
    ∪-idʳ-alg .fst ⟅⟆ = refl
    ∪-idʳ-alg .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (w ▹ x ∷_) P⟨xs⟩

  ∪-com : ∀ xs ys → xs ∪ ys ≡ ys ∪ xs
  ∪-com xs ys = ⟦ ∪-com-alg ys ⟧ xs
    where
    ∪-com-alg : ∀ ys → Ψ[ xs ⦂ Weighted A ] ↦ (xs ∪ ys ≡ ys ∪ xs)
    ∪-com-alg ys .snd = eq-coh
    ∪-com-alg ys .fst ⟅⟆ = sym (∪-idʳ ys)
    ∪-com-alg ys .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
      w ▹ x ∷ xs ∪ ys ≡⟨ cong (w ▹ x ∷_) P⟨xs⟩ ⟩
      w ▹ x ∷ ys ∪ xs ≡⟨ ∪-cons w x ys xs ⟩
      ys ∪ w ▹ x ∷ xs ∎ 

  commutativeMonoid : CommutativeMonoid (Weighted A)
  commutativeMonoid .CommutativeMonoid.monoid .Monoid._∙_ = _∪_
  commutativeMonoid .CommutativeMonoid.monoid .Monoid.ε = ⟅⟆
  commutativeMonoid .CommutativeMonoid.monoid .Monoid.assoc = ∪-assoc
  commutativeMonoid .CommutativeMonoid.monoid .Monoid.ε∙ _ = refl
  commutativeMonoid .CommutativeMonoid.monoid .Monoid.∙ε = ∪-idʳ
  commutativeMonoid .CommutativeMonoid.comm = ∪-com

  infix 4 _⊆_
\end{code}
%<*subset>
\begin{code}
  _⊆_ : Weighted A → Weighted A → Type-
  xs ⊆ ys = xs ∪ ys ≡ ys
\end{code}
%</subset>
\begin{code}

  ⊆-trans : ∀ xs ys zs → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
  ⊆-trans xs ys zs xs⊆ys ys⊆zs =
    xs ∪ zs ≡˘⟨ cong (xs ∪_) ys⊆zs ⟩
    xs ∪ (ys ∪ zs) ≡˘⟨ ∪-assoc xs ys zs ⟩
    (xs ∪ ys) ∪ zs ≡⟨ cong (_∪ zs) xs⊆ys ⟩
    ys ∪ zs ≡⟨ ys⊆zs ⟩
    zs ∎

  []⊆ : ∀ xs → ⟅⟆ ⊆ xs
  []⊆ _ = refl

  ⊆-cons : ∀ w (x : A) xs ys → xs ⊆ ys → xs ⊆ w ▹ x ∷ ys
  ⊆-cons w x xs ys xs⊆ys = sym (∪-cons w x xs ys) ; cong (w ▹ x ∷_) xs⊆ys

record _⟶W_ (A : Type a) (B : Type b) : Type (ℓ ℓ⊔ a ℓ⊔ b) where
  no-eta-equality
  field
    act-w : 𝑆 → A → Weighted B
    coh-w : ∀ p q x → act-w p x ∪ act-w q x ≡ act-w (p ∙ q) x
open _⟶W_ public

infixl 6 _[_]W⊣_
_[_]W⊣_ : 𝑆 → A ⟶W B → A → Weighted B
_[_]W⊣_ = flip act-w


[_]W-hom : A ⟶W B → A W⟶ Weighted B
[ h ]W-hom = record
  { w-mon = commutativeMonoid
  ; w-set = trunc
  ; w-act = act-w h
  ; w-coh = coh-w h
  }

[_]W↓ : A ⟶W B → Weighted A → Weighted B
[ h ]W↓ = W[ [ h ]W-hom ]↓

module _ {A : Type a} {B : Type b} where
  collect-∪ : (h : A ⟶W B) (xs ys : Weighted A) → [ h ]W↓ (xs ∪ ys) ≡ [ h ]W↓ xs ∪ [ h ]W↓ ys
  collect-∪ h xs ys = ⟦ alg ⟧ xs
    where
    alg : Ψ[ xs ⦂ Weighted A ] ↦ [ h ]W↓ (xs ∪ ys) ≡ [ h ]W↓ xs ∪ [ h ]W↓ ys
    alg .fst ⟅⟆ = refl
    alg .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (w [ h ]W⊣ x ∪_) P⟨xs⟩ ; sym (∪-assoc (w [ h ]W⊣ x) ([ h ]W↓ xs) ([ h ]W↓ ys))
    alg .snd = eq-coh


module ⟶W-Eq {A : Type a} {B : Type b} where
  ⟶W′ : Type _
  ⟶W′ = Σ[ kont ⦂ (𝑆 → A → Weighted B) ] × (∀ p q x → kont p x ∪ kont q x ≡ kont (p ∙ q) x)

  toSigma : (A ⟶W B) → ⟶W′
  toSigma x = x .act-w , x .coh-w

  fromSigma : ⟶W′ → (A ⟶W B)
  fromSigma x = record
    { act-w = x .fst
    ; coh-w = x .snd
    }

  sigma-iso : (A ⟶W B) ⇔ ⟶W′
  sigma-iso .fun = toSigma
  sigma-iso .inv = fromSigma
  sigma-iso .rightInv x = refl
  sigma-iso .leftInv x i .act-w = x .act-w
  sigma-iso .leftInv x i .coh-w = x .coh-w

  ⟶W-≡ : (x y : A ⟶W B) → (∀ w v → act-w x w v ≡ act-w y w v) → x ≡ y
  ⟶W-≡ x y p = sym (sigma-iso .leftInv x)
              ; cong fromSigma (Σ≡Prop (λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → trunc _ _) (funExt λ w → funExt (p w)))
              ; sigma-iso .leftInv y
open ⟶W-Eq using (⟶W-≡) public

module _ {A : Type a} {B : Type b} where
  fold-⊕-hom : ∀ (h : A W⟶ B) x y → W[ h ]↓ x W[ h ]⊕ W[ h ]↓ y ≡ W[ h ]↓ (x ∪ y)
  fold-⊕-hom h xs ys = ⟦ alg ys ⟧ xs
    where
    alg : ∀ ys → Ψ[ xs ⦂ Weighted A ] ↦ W[ h ]↓ xs W[ h ]⊕ W[ h ]↓ ys ≡ W[ h ]↓ (xs ∪ ys)
    alg ys .fst ⟅⟆ = W[ h ]-ε∙ _
    alg ys .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
      W[ h ]↓ (w ▹ x ∷ xs) W[ h ]⊕ W[ h ]↓ ys ≡⟨⟩
      w W[ h ]⊣ x W[ h ]⊕  W[ h ]↓ xs W[ h ]⊕ W[ h ]↓ ys ≡⟨ W[ h ]-assoc _ _ _ ⟩
      w W[ h ]⊣ x W[ h ]⊕ (W[ h ]↓ xs W[ h ]⊕ W[ h ]↓ ys) ≡⟨ cong (w W[ h ]⊣ x W[ h ]⊕_) P⟨xs⟩ ⟩
      w W[ h ]⊣ x W[ h ]⊕  W[ h ]↓ (xs ∪ ys) ≡⟨⟩
      W[ h ]↓ (w ▹ x ∷ xs ∪ ys) ∎
    alg ys .snd = prop-coh λ _ → w-set h _ _

  fold-ε-hom : (h : A W⟶ B) → W[ h ]↓ ⟅⟆ ≡ W[ h ]-ε
  fold-ε-hom _ = refl

module _ {A : Type a} {B : Type b} {C : Type c} where
  infixl 9 _W∘_
  _W∘_ : B W⟶ C → A ⟶W B → A W⟶ C
  (b→c W∘ a→b) .w-mon = b→c .w-mon
  (b→c W∘ a→b) .w-set = b→c .w-set
  (b→c W∘ a→b) .w-act s x = W[ b→c ]↓ (s [ a→b ]W⊣ x)
  (b→c W∘ a→b) .w-coh p q x =
    W[ b→c ]↓ (p [ a→b ]W⊣ x) W[ b→c ]⊕ W[ b→c ]↓ (q [ a→b ]W⊣ x) ≡⟨ fold-⊕-hom b→c (p [ a→b ]W⊣ x) (q [ a→b ]W⊣ x) ⟩
    W[ b→c ]↓ (p [ a→b ]W⊣ x ∪ q [ a→b ]W⊣ x) ≡⟨ cong W[ b→c ]↓ (coh-w a→b p q x) ⟩
    W[ b→c ]↓ (p ∙ q [ a→b ]W⊣ x) ∎

  module _ (b→c : B W⟶ C) (a→b : A ⟶W B) where
    W-comp-eq : ∀ x → W[ b→c W∘ a→b ]↓ x ≡ W[ b→c ]↓ ([ a→b ]W↓ x)
    W-comp-eq = ⟦ alg ⟧
      where
      alg : Ψ[ x ⦂ Weighted A ] ↦ W[ b→c W∘ a→b ]↓ x ≡ W[ b→c ]↓ ([ a→b ]W↓ x)
      alg .fst ⟅⟆ = refl
      alg .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
        W[ b→c W∘ a→b ]↓ (w ▹ x ∷ xs) ≡⟨⟩
        W[ b→c ]↓ (w [ a→b ]W⊣ x) W[ b→c ]⊕ W[ b→c W∘ a→b ]↓ xs ≡⟨ cong (W[ b→c ]↓ (w [ a→b ]W⊣ x) W[ b→c ]⊕_) P⟨xs⟩ ⟩
        W[ b→c ]↓ (w [ a→b ]W⊣ x) W[ b→c ]⊕ W[ b→c ]↓ ([ a→b ]W↓ xs) ≡⟨ fold-⊕-hom b→c (w [ a→b ]W⊣ x) ([ a→b ]W↓ xs) ⟩
        W[ b→c ]↓ (w [ a→b ]W⊣ x ∪ [ a→b ]W↓ xs) ≡⟨⟩
        W[ b→c ]↓ ([ a→b ]W↓ (w ▹ x ∷ xs)) ∎
      alg .snd = prop-coh λ _ → w-set b→c _ _

W⟶id : A ⟶W A
W⟶id .act-w p x = p ▹ x ∷ ⟅⟆
W⟶id .coh-w p q x = dup p q x ⟅⟆

W⟶id-id : (x : Weighted A) → [ W⟶id ]W↓ x ≡ x
W⟶id-id = ⟦ alg ⟧
  where
  alg : Ψ[ x ⦂ Weighted A ] ↦ [ W⟶id ]W↓ x ≡ x
  alg .snd = eq-coh
  alg .fst ⟅⟆ = refl
  alg .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (w ▹ x ∷_) P⟨xs⟩

hom-inj : {A : Type a} → (x y : Weighted A) → (∀ {B : Type (ℓ ℓ⊔ a)} (f : A W⟶ B) → W[ f ]↓ x ≡ W[ f ]↓ y) → x ≡ y
hom-inj x y p = sym (W⟶id-id x) ; p [ W⟶id ]W-hom ; W⟶id-id y

null : Weighted A → Bool
null = ⟦ alg ⟧
  where
  alg : Ψ[ x ⦂ Weighted A ] ↦ Bool
  alg .fst ⟅⟆ = true
  alg .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = false
  alg .snd .c-set _ = isSetBool
  alg .snd .c-dup p q x xs ψ⟨xs⟩ = refl
  alg .snd .c-com p x q y xs ψ⟨xs⟩ = refl
\end{code}
