\begin{code}
{-# OPTIONS --safe --lossy-unification #-}

open import Prelude renaming ([_] to [_]⊩)
open import Algebra
open import Algebra.Monus

-- try remove cancellative requirement (probably can't)

module Codata.Neighbours
  {W : Type} (mon : WellFoundedMonus W)
  where

open WellFoundedMonus mon

open Weight (weight W tapom)

open import Data.Weighted ⊕-semigroup hiding (⟪_⟫)
open import Data.Weighted.Monad (weight W tapom) renaming (return to ηʷ)
import Data.Weighted.Monad (weight _ tapom) as WB
open import Data.Weighted.Functor
open import Data.Weighted.Cutoff totalOrder
open import Data.Weighted.CutoffMonus tmapom

open import Path.Reasoning

≤-⋊-⊢ : ∀ w (s : Weighted A) v → (w≤v : w ≤ v) → (w ⋊ s) ⊢ v ≡ w ⋊ (s ⊢ w≤v .fst)
≤-⋊-⊢ w s v w≤v = ⟦ alg w v w≤v ⟧ s
  where
  alg : ∀ w v → (w≤v : w ≤ v) → Ψ[ s ⦂ Weighted A ] ↦ (w ⋊ s) ⊢ v ≡ w ⋊ (s ⊢ w≤v .fst)
  alg w v w≤v .snd = eq-coh
  alg w v w≤v .fst ⟅⟆ = refl
  alg w v (k , v≡w∙k) .fst (u ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) with w ∙ u ≤? v | u ≤? k
  ... | yes w∙u≤v | yes u≤k = cong (w ∙ u ▹ x ∷_) P⟨xs⟩
  ... | no  w∙u≰v | no  u≰k = P⟨xs⟩
  ... | no  w∙u≰v | yes u≤k = absurd (w∙u≰v ≲[ ≤[ ≤-cong w u≤k ] ≲; ≡[ sym v≡w∙k ] ])
  ... | yes w∙u≤v | no  u≰k = absurd (u≰k (≤-cancelˡ w _ _ ≲[ ≤[ w∙u≤v ] ≲; ≡[ v≡w∙k ] ]))

Neighbours′ : Type → Type
Neighbours′ A = W → Weighted A

\end{code}
%<*neighbourly>
\begin{code}
Neighbourly : (W → Weighted A) → Type-
Neighbourly f =
  ∀ v w → v ≥ w → f v ⊢ w ≡ f w
\end{code}
%</neighbourly>
\begin{code}

NeighbourlyAt : Neighbours′ A → W → W → Type _
NeighbourlyAt s v w = v ≥ w → s v ⊢ w ≡ s w

Action : Neighbours′ A → Type _
Action s = ∀ v w → s v ⊢ w ≡ s (v ⊓ w)

ActionAt : Neighbours′ A → W → W → Type _
ActionAt s v w = s v ⊢ w ≡ s (v ⊓ w)

at-action-prec : ∀ (s : Neighbours′ A) v w → ActionAt s v w → NeighbourlyAt s v w
at-action-prec s v w asc w≥v = asc ; cong s (⊓-comm v w ; ⊓≤≡ _ _ w≥v)

action-prec : (s : Neighbours′ A) → Action s → Neighbourly s
action-prec s asc v w = at-action-prec s v w (asc v w)

private module TypeDef where
  record Neighbours (A : Type) : Type
\end{code}
%<*neighbours-type>
\begin{code}
  record Neighbours A where
    field  _⊩_      : W → Weighted A
           neighbourly  : Neighbourly _⊩_
\end{code}
%</neighbours-type>
\begin{code}

prec-act : ∀ (s : Neighbours′ A) → Neighbourly s → Action s
prec-act s⊢ prec v w with v <? w
... | no  v≮w = prec _ _ (≮⇒≥ v≮w)
... | yes v<w =
  s⊢ v ⊢ w     ≡˘⟨ cong (_⊢ w) (prec _ _ (<⇒≤ v<w)) ⟩
  s⊢ w ⊢ v ⊢ w ≡⟨ ⊢-com (s⊢ w) v w ⟩
  s⊢ w ⊢ w ⊢ v ≡⟨ ⊢-≥ (s⊢ w) _ _ (<⇒≤ v<w)  ⟩
  s⊢ w ⊢ v     ≡⟨ prec _ _ (<⇒≤ v<w) ⟩
  s⊢ v ∎

record Neighbours (A : Type) : Type where
  no-eta-equality
  infix 11 _⊩_
  field
    _⊩_ : W → Weighted A
    neighbourly : Neighbourly _⊩_

  acts : Action _⊩_
  acts = prec-act _⊩_ neighbourly

open Neighbours public

module NeighboursEq {A : Type} where
  Neighbours″ : Type
  Neighbours″ = Σ (W → Weighted A) Neighbourly

  to-sigma : Neighbours A → Neighbours″
  to-sigma s = _⊩_ s , neighbourly s

  from-sigma : Neighbours″ → Neighbours A
  from-sigma s ⊩ w = s .fst w
  from-sigma s .neighbourly = snd s

  to∘from : ∀ x → to-sigma (from-sigma x) ≡ x
  to∘from x = refl

  from∘to : ∀ x → from-sigma (to-sigma x) ≡ x
  from∘to x i ._⊩_ = _⊩_ x
  from∘to x i .neighbourly = x .neighbourly

  open import Cubical.Data.Sigma using (Σ≡Prop)

  search≡ : {x y : Neighbours A} → (∀ w → x ⊩ w ≡ y ⊩ w) → x ≡ y
  search≡ {x} {y} p =
      sym (from∘to x)
    ; cong from-sigma (Σ≡Prop (λ s → isPropΠ λ w → isPropΠ λ v → isProp→ (trunc (s w ⊢ v) (s v))) (funExt p))
    ; from∘to y

  isSetNeighbours : isSet (Neighbours A)
  isSetNeighbours =
    subst isSet (isoToPath (iso from-sigma to-sigma from∘to to∘from)) $
      isSetΣ {A = W → Weighted A}
             {B = Neighbourly}
             (isSetΠ (λ _ → trunc))
             λ _ → isSetΠ λ _ → isSetΠ λ _ → isSetΠ λ _ → isProp→isSet (trunc _ _)
open NeighboursEq using (search≡; isSetNeighbours) public

infix 4 _⊑ˢ_
_⊑ˢ_ : Neighbours A → Neighbours A → Type-
x ⊑ˢ y = ∀ d → x ⊩ d ⊑ y ⊩ d
⊑ˢ-refl : (x : Neighbours A) → x ⊑ˢ x
⊑ˢ-refl x d = d , sym (neighbourly x d d ≤-refl) 

⊑ˢ-trans : {x y z : Neighbours A} → x ⊑ˢ y → y ⊑ˢ z → x ⊑ˢ z
⊑ˢ-trans {z = z} x⊑y y⊑z d =
  let k₁ , x⊩d≡y⊩d⊢k₁ = x⊑y d
      k₂ , y⊩d≡z⊩d⊢k₂ = y⊑z d
  in k₂ ⊓ k₁ , (x⊩d≡y⊩d⊢k₁ ; cong (_⊢ k₁) y⊩d≡z⊩d⊢k₂ ; ⊢-⊓ (z ⊩ d) k₂ k₁)

⊑ˢ-antisym : {x y : Neighbours A} → x ⊑ˢ y → y ⊑ˢ x → x ≡ y
⊑ˢ-antisym x⊑ˢy y⊑ˢx = search≡ λ w → ⊑-antisym (x⊑ˢy w) (y⊑ˢx w)

module _ where
  open import Data.Weighted.Syntax ⊓-semigroup

\end{code}
%<*return>
\begin{code}
  η : A → Neighbours A
  η x ⊩ _ = ⟅ ε ▹ x ⟆
  η x .neighbourly v w v≥w = η-lemma
\end{code}
%</return>
\begin{code}
    where
    η-lemma : ⟅ ε ▹ x ⟆ ⊢ w ≡ ⟅ ε ▹ x ⟆
    η-lemma with ε ≤? w
    ... | yes _   = refl
    ... | no ε≰w  = absurd (ε≰w (w , sym (ε∙ w)))
\end{code}
%<*searched>
\begin{code}
searched : Weighted A → Neighbours A
searched xs ⊩ w = xs ⊢ w
\end{code}
%</searched>
\begin{code}
searched xs .neighbourly  = ⊢-≥ xs 

infixl 6 _⊪_
\end{code}
%<*bind-upto>
\begin{code}
_⊪_ :  Weighted (Neighbours A) →
       W → Weighted A
s ⊪ w = s >>= _⊩ w
\end{code}
%</bind-upto>
\begin{code}
open import Path.Reasoning

join-prec : (s : Neighbours (Neighbours A)) →
\end{code} 
%<*join-prec>
\begin{code}
          ∀ v w → v ≥ w → s ⊩ v ⊪ v ⊢ v ⊢ w ≡ s ⊩ w ⊪ w ⊢ w
\end{code} 
%</join-prec>
\begin{code}
join-prec s v w v≥w =
\end{code}
%<*join-prec-proof>
\begin{code}
  s ⊩ v ⊪ v ⊢ v ⊢ w          ≡⟨ ⊢-≥ (s ⊩ v ⊪ v) v w v≥w ⟩
  s ⊩ v ⊪ v ⊢ w              ≡⟨ >>=-⊢ʳ w (s ⊩ v) (_⊩ v) ⟩
  (s ⊩ v >>= _⊩ v ∘⊢ w) ⊢ w  ≡⟨ cong (λ e → (s ⊩ v >>= e) ⊢ w) (funExt λ s → neighbourly s v w v≥w) ⟩
  s ⊩ v ⊪ w ⊢ w              ≡⟨ >>=-⊢ˡ w (s ⊩ v) (_⊩ w) ⟩
  s ⊩ v ⊢ w ⊪ w ⊢ w          ≡⟨ cong (λ e → e ⊪ w ⊢ w) (neighbourly s v w v≥w) ⟩
  s ⊩ w ⊪ w ⊢ w ∎
\end{code}
%</join-prec-proof>
\begin{code}

private variable X : Type

\end{code}
%<*join-impl>
\begin{code}
μ :  Neighbours (Neighbours A) →
     Neighbours A
μ s ⊩ w = s ⊩ w ⊪ w ⊢ w
\end{code}
%</join-impl>
\begin{code}
neighbourly (μ s) = join-prec s

\end{code}
%<*mapn-ty>
\begin{code}
mapₙ :  (A → B) →
        (Neighbours A → Neighbours B)
\end{code}
%</mapn-ty>
\begin{code}
mapₙ f s ⊩ w = wmap f (s ⊩ w)
mapₙ f s .neighbourly v w v≥w =
  wmap f (s ⊩ v) ⊢ w ≡˘⟨ W-comp-eq [ w ⊣-alg ]W-hom (wmap-alg f) (s ⊩ v) ⟩
  W[ [ w ⊣-alg ]W-hom W∘ wmap-alg f ]↓ (s ⊩ v)

    ≡⟨ cong (λ e → W[ e ]↓ (s ⊩ v)) (W⟶-≡ ([ w ⊣-alg ]W-hom W∘ wmap-alg f) ([ wmap-alg f ]W-hom W∘ w ⊣-alg) lemma (λ _ _ → refl) refl) ⟩

  W[ [ wmap-alg f ]W-hom W∘ w ⊣-alg ]↓ (s ⊩ v) ≡⟨ W-comp-eq [ wmap-alg f ]W-hom (w ⊣-alg) (s ⊩ v) ⟩
  wmap f (s ⊩ v ⊢ w) ≡⟨ cong (wmap f) (s .neighbourly v w v≥w) ⟩
  wmap f (s ⊩ w) ∎
  where
  lemma : ∀ p x → (p ▹ f x ∷ ⟅⟆) ⊢ w ≡ wmap f (w / p ▹ x)
  lemma p x with p ≤ᵇ w
  ... | false = refl
  ... | true = refl

≺-shift : (s p w : W) → (p≺w : [ s ] p ≺ w) → [ s ] p≺w .fst ≺ w
≺-shift s p w (k , w≡p∙s∙k) = p , (w≡p∙s∙k ; assoc p s k ; cong (p ∙_) (comm s k) ; comm p (k ∙ s))

lemma-⊓₁ : ∀ p q s → p ≤ q → (q ∙ s ∙ ε) ⊓ (p ∙ s ∙ ε) ≡ p ∙ s ∙ ε
lemma-⊓₁ p q s p≤q = 
  (q ∙ s ∙ ε) ⊓ (p ∙ s ∙ ε) ≡⟨ ⊓-comm (q ∙ s ∙ ε) (p ∙ s ∙ ε) ⟩
  (p ∙ s ∙ ε) ⊓ (q ∙ s ∙ ε) ≡˘⟨ ⟨⊓⟩∙ (p ∙ s) (q ∙ s) ε ⟩
  ((p ∙ s) ⊓ (q ∙ s)) ∙ ε ≡⟨ cong (_∙ ε) (⊓≤≡ (p ∙ s) (q ∙ s) (≤-congʳ s p≤q)) ⟩
  p ∙ s ∙ ε ∎

\end{code}
%<*rtimes-n>
\begin{code}
_⋊ₙ_ : W → Neighbours A → Neighbours A
(w ⋊ₙ s) ⊩ v with w ≤? v
... | yes (v∸w , _) = w ⋊ s ⊩ v∸w
... | no _ = ⟅⟆
\end{code}
%</rtimes-n>
\begin{code}
(w ⋊ₙ s) .neighbourly u v u≥v with w ≤? u | w ≤? v
... | no  w≰u | no  w≰v = refl
... | yes (k , _) | no w≰v = >-⋊-⊢ w (s ⊩ k) v w≰v
... | no  w≰u | yes w≤v = absurd (w≰u ≲[ ≤[ w≤v ] ≲; ≤[ u≥v ] ])
... | yes (k₁ , u≡w∙k₁) | yes (k₂ , v≡w∙k₂) =
  (w ⋊ s ⊩ k₁) ⊢ v  ≡⟨ ≤-⋊-⊢ w (s ⊩ k₁) v (k₂ , v≡w∙k₂) ⟩
  w ⋊ (s ⊩ k₁ ⊢ k₂) ≡⟨ cong (w ⋊_) (s .neighbourly k₁ k₂ (u≥v .fst , cancelˡ w k₁ (k₂ ∙ u≥v .fst) (sym u≡w∙k₁ ; u≥v .snd ; cong (_∙ u≥v .fst) v≡w∙k₂ ; assoc w k₂ _))) ⟩
  w ⋊ s ⊩ k₂ ∎

module _ {A B : Type} (f : A → B) where
  mapₙ-⋊ₙ : ∀ s x → s ⋊ₙ mapₙ f x ≡ mapₙ f (s ⋊ₙ x)
  mapₙ-⋊ₙ s x = search≡ (lemma s x)
    where
    lemma : ∀ s x w → (s ⋊ₙ mapₙ f x) ⊩ w ≡ mapₙ f (s ⋊ₙ x) ⊩ w
    lemma s x w with s ≤? w
    ... | no _ = refl
    ... | yes (k , w≡s∙k) = wmap-⋊ s f (x ⊩ k)

module _ {A : Type} where
  μ-⋊ : ∀ s (x : Neighbours (Neighbours A)) → μ (s ⋊ₙ x) ≡ (s ⋊ₙ μ x)
  μ-⋊ s x = search≡ (lemma s x)
    where
    lemma : ∀ s x w → μ (s ⋊ₙ x) ⊩ w ≡ (s ⋊ₙ μ x) ⊩ w
    lemma s x w with s ≤? w
    ... | no _ = refl
    ... | yes (k , w≡s∙k) =
      (s ⋊ x ⊩ k) ⊪ w ⊢ w ≡⟨ cong (_⊢ w) (⋊->>= s (x ⊩ k) (_⊩ w)) ⟩
      (s ⋊ x ⊩ k ⊪ w) ⊢ w ≡⟨ ≤-⋊-⊢ s (x ⊩ k ⊪ w) w (k , w≡s∙k) ⟩
      s ⋊ x ⊩ k ⊪ w ⊢ k ≡⟨ cong (s ⋊_) (>>=-⊢ʳ k (x ⊩ k) (_⊩ w)) ⟩
      s ⋊ (x ⊩ k >>= _⊩ w ∘⊢ k) ⊢ k ≡⟨ cong (λ e → s ⋊ (x ⊩ k >>= e) ⊢ k) (funExt λ y → neighbourly y w k (s , (w≡s∙k ; comm s k)) ) ⟩
      s ⋊ x ⊩ k ⊪ k ⊢ k ∎

\end{code}
%<*heavier>
\begin{code}
Heavier : W → Neighbours A → Type-
Heavier w x = ∃ lighter × x ≡ w ⋊ₙ lighter
\end{code}
%</heavier>
\begin{code}

module IdealS (s : W) where
  open import Cubical.Data.Sigma.Properties using (Σ-assoc-Iso)

  INeighbours : Type → Type
\end{code}
%<*ineighbours-sigma>
\begin{code}
  INeighbours A =
    Σ[ x ⦂ Neighbours A ] × Heavier s x
\end{code}
%</ineighbours-sigma>
\begin{code}

  INeighbours′ : Type → Type
  INeighbours′ A = Σ (Neighbours A × Neighbours A) (λ { (x , y) → x ≡ s ⋊ₙ y })

  to-implicit : INeighbours′ A → Neighbours A
  to-implicit ((_ , y) , _) = y

  from-implicit : Neighbours A → INeighbours′ A
  from-implicit x = (s ⋊ₙ x , x) , refl

  isearch-iso′ : Neighbours A ⇔ INeighbours′ A
  isearch-iso′ .fun = from-implicit
  isearch-iso′ .inv = to-implicit
  isearch-iso′ .rightInv ((x , y) , p) = Σ≡Prop (λ _ →  isSetNeighbours _ _) (cong₂ _,_ (sym p) refl)
  isearch-iso′ .leftInv  x = refl

  isearch-iso : Neighbours A ⇔ INeighbours A
  isearch-iso = trans-⇔ isearch-iso′ Σ-assoc-Iso
open IdealS using (isearch-iso) public

INeighbours : Type → Type
INeighbours = Neighbours

module Solve (s : W) (s≢ε : s ≢ ε) (eᵢ : (X → INeighbours (X ⊎ A) ⊎ A)) where
  infix 4 _≺ₛ_
  _≺ₛ_ : W → W → Type
  _≺ₛ_ = [ s ]_≺_

  private module sigma where
\end{code}
%<*sigma>
\begin{code}
    σ : INeighbours A → Neighbours A
    σ x = s ⋊ₙ x
\end{code}
%</sigma>
\begin{code}

  cut     : ∀ w → Acc _≺ₛ_ w → Weighted (X ⊎ A) → Weighted A
  cut-to  : ∀ w → Acc _≺ₛ_ w → W → X ⊎ A → Weighted A
  step    : ∀ w p → p ≺ₛ w → Acc _≺ₛ_ w → X ⊎ A → Weighted A
  cut-alg : ∀ w → Acc _≺ₛ_ w → (X ⊎ A) ⟶W A
\end{code}
%<*find>
\begin{code}
  find    : ∀ w → Acc _≺ₛ_ w → X → Weighted A
  find w wf = (cut w wf ∘ _⊩ w ▿ ηʷ) ∘ eᵢ
\end{code}
%</find>
%<*cut-to>
\begin{code}
  cut-to w wf p x with p ∙ s ≤? w
  ... | yes p∙s≤w = p ∙ s ⋊ step w p p∙s≤w wf x
  ... | no _ = ⟅⟆
\end{code}
%</cut-to>
\begin{code}
  cut   w wf = [ cut-alg w wf ]W↓
\end{code}
%<*step>
\begin{code}
  step w p p≺w wf        (inr  x) = ηʷ x
  step w p p≺w (acc wf)  (inl  x) = find (p≺w .fst) (wf _ (≺-shift s p w p≺w)) x
\end{code}
%</step>
%<*cut-coh>
\begin{code}
  cut-coh : ∀ w wf p q x →
    cut-to w wf p x ∪ cut-to w wf q x ≡
      cut-to w wf (p ⊓ q) x
\end{code}
%</cut-coh>
\begin{code}

  cut-alg w wf = record { act-w = cut-to w wf; coh-w = cut-coh w wf }

\end{code}
%<*cut-neighbourly>
\begin{code}
  cut-neighbourly :  ∀ k₁ k₂ wf₁ wf₂ x →
                 k₁ ≥ k₂ →
                 cut k₂ wf₂ (x ⊩ k₂) ≡ cut k₁ wf₁ (x ⊩ k₁) ⊢ k₂
\end{code}
%</cut-neighbourly>
%<*cut-absorbs>
\begin{code}
  cut-absorbs :  ∀ w wf p q x →
                 p ≤ q →
                 cut-to w wf q x ⊆ cut-to w wf p x
\end{code}
%</cut-absorbs>
%<*find-neighbourly>
\begin{code}
  find-neighbourly :  ∀ d₁ d₂ wf₁ wf₂ x →
                  d₁ ≥ d₂ →
                  find d₁ wf₁ x ⊢ d₂ ≡ find d₂ wf₂ x
\end{code}
%</find-neighbourly>
\begin{code}

  step-neighbourly : ∀ p k₁ k₂ wf₁ wf₂ v (p≺k₁ : p ≺ₛ k₁) (p≺k₂ : p ≺ₛ k₂)
               → k₁ ≥ k₂
               → step k₁ p p≺k₁ wf₁ v ⊢ p≺k₂ .fst ≡ step k₂ p p≺k₂ wf₂ v

  cut-com : ∀ k₁ k₂ wf₁ wf₂
          → k₂ ≤ k₁
          → ∀ p v
          → cut k₂ wf₂ (k₂ / p ▹ v) ≡ cut-to k₁ wf₁ p v ⊢ k₂

  cut-coh w wf p q x with p <? q
  ... | yes p<q = ∪-com (cut-to w wf p x) (cut-to w wf q x) ; cut-absorbs w wf p q x (<⇒≤ p<q)
  ... | no  p≮q = cut-absorbs w wf q p x (≮⇒≥ p≮q)

  cut-absorbs w wf p q x p≤q with p ∙ s ≤? w | q ∙ s ≤? w
  cut-absorbs w wf p q x p≤q | yes p∙s≤w | no  q∙s≰w = refl 
  cut-absorbs w wf p q x p≤q | no  p∙s≰w | no  q∙s≰w = ∪-idʳ _
  cut-absorbs w wf p q x p≤q | no  p∙s≰w | yes q∙s≤w = absurd (p∙s≰w ≲[ ≤[ ≤-congʳ s p≤q ] ≲; ≤[ q∙s≤w ] ])
  cut-absorbs w wf p q (inr x) p≤q | yes p∙s≤w | yes q∙s≤w = dup (q ∙ s ∙ ε) (p ∙ s ∙ ε) x ⟅⟆ ; cong (_▹ x ∷ ⟅⟆) (lemma-⊓₁ p q s p≤q)
  cut-absorbs w (acc wf) p q (inl x) p≤q | yes p∙s≤w | yes q∙s≤w with eᵢ x
  cut-absorbs w (acc wf) p q (inl x) p≤q | yes p∙s≤w | yes q∙s≤w | inr y = dup (q ∙ s ∙ ε) (p ∙ s ∙ ε) y ⟅⟆ ; cong (_▹ y ∷ ⟅⟆) (lemma-⊓₁ p q s p≤q)
  cut-absorbs w (acc wf) p q (inl x) (k , q≡p∙k) | yes (k₁ , w≡p∙s∙k₁) | yes (k₂ , w≡q∙s∙k₂) | inl y =
    let wf₁ = wf k₁ (≺-shift s p w (k₁ , w≡p∙s∙k₁))
        wf₂ = wf k₂ (≺-shift s q w (k₂ , w≡q∙s∙k₂))
        lemma = cancelˡ (p ∙ s) k₁ (k₂ ∙ k) $
          p ∙ s ∙ k₁ ≡˘⟨ w≡p∙s∙k₁ ⟩
          w          ≡⟨ w≡q∙s∙k₂ ⟩
          q ∙ s ∙ k₂ ≡⟨ cong (λ e → e ∙ s ∙ k₂) q≡p∙k ⟩
          ((p ∙ k) ∙ s) ∙ k₂ ≡⟨ assoc (p ∙ k) s k₂ ⟩
          (p ∙ k) ∙ (s ∙ k₂) ≡⟨ assoc p k (s ∙ k₂) ⟩
          p ∙ (k ∙ (s ∙ k₂)) ≡⟨ cong (p ∙_) (comm k (s ∙ k₂)) ⟩
          p ∙ ((s ∙ k₂) ∙ k) ≡⟨ cong (p ∙_) (assoc s k₂ k) ⟩
          p ∙ (s ∙ (k₂ ∙ k)) ≡˘⟨ assoc p s (k₂ ∙ k) ⟩
          (p ∙ s) ∙ (k₂ ∙ k) ∎
    in ⋊-∪-⋊ (cut k₁ wf₁ (y ⊩ k₁))
              (cut k₂ wf₂ (y ⊩ k₂))
              (p ∙ s)
              (q ∙ s)
              (≤-congʳ s (k , q≡p∙k))
              (k₂ , cut-neighbourly k₁ k₂ wf₁ wf₂ y (k , lemma))

  find-neighbourly d₁ d₂ wf₁ wf₂ x d₁≥d₂ with eᵢ x
  ... | inr y = return-⊢ y d₂
  ... | inl y = sym (cut-neighbourly d₁ d₂ wf₁ wf₂ y d₁≥d₂)

  step-neighbourly p k₁ k₂ wf₁ wf₂ (inr x) p∙s≤k₁ p∙s≤k₂ _ = return-⊢ x (p∙s≤k₂ .fst)
  step-neighbourly p k₁ k₂ (acc wf₁) (acc wf₂) (inl x) p∙s≤k₁ p∙s≤k₂ (k₃ , k₁≡k₂∙k₃) =
    find-neighbourly
      (p∙s≤k₁ .fst)
      (p∙s≤k₂ .fst)
      (wf₁ _ (≺-shift s p k₁ p∙s≤k₁))
      (wf₂ _ (≺-shift s p k₂ p∙s≤k₂))
      x
      (k₃ , cancelˡ (p ∙ s) _ _ (sym (p∙s≤k₁ .snd) ; k₁≡k₂∙k₃ ; cong (_∙ k₃) (p∙s≤k₂ .snd) ; assoc _ _ k₃))

  cut-com k₁ k₂ wf₁ wf₂ k₂≤k₁ p v with p ≤? k₂ 
  ... | no  p≰k₂ with p ∙ s ≤? k₁
  ... | no _ = refl
  ... | yes p∙s≤k₁ = sym (>-⋊-⊢ (p ∙ s) (step k₁ p p∙s≤k₁ wf₁ v) k₂ ≲[ <[ p≰k₂ ] ≲; ≤[ x≤x∙y ] ])
  cut-com k₁ k₂ wf₁ wf₂ k₂≤k₁ p v | yes p≤k₂ with p ∙ s ≤? k₁ | p ∙ s ≤? k₂
  ... | no  p∙s≰k₁ | no _ = refl
  ... | no  p∙s≰k₁ | yes p∙s≤k₂ = absurd (p∙s≰k₁ ≲[ ≤[ p∙s≤k₂ ] ≲; ≤[ k₂≤k₁ ] ])
  ... | yes p∙s≤k₁ | no  p∙s≰k₂ = sym (>-⋊-⊢ (p ∙ s) (step k₁ p p∙s≤k₁ wf₁ v) k₂ p∙s≰k₂)
  ... | yes p∙s≤k₁ | yes p∙s≤k₂ =
    (p ∙ s ⋊ step k₂ p p∙s≤k₂ wf₂ v) ∪ ⟅⟆          ≡⟨ ∪-idʳ _ ⟩
    p ∙ s ⋊ step k₂ p p∙s≤k₂ wf₂ v                 ≡˘⟨ cong (p ∙ s ⋊_) (step-neighbourly p k₁ k₂ wf₁ wf₂ v p∙s≤k₁ p∙s≤k₂ k₂≤k₁) ⟩
    p ∙ s ⋊ (step k₁ p p∙s≤k₁ wf₁ v ⊢ p∙s≤k₂ .fst) ≡˘⟨ ≤-⋊-⊢ (p ∙ s) (step k₁ p p∙s≤k₁ wf₁ v) k₂ p∙s≤k₂ ⟩
    (p ∙ s ⋊ step k₁ p p∙s≤k₁ wf₁ v) ⊢ k₂ ∎

  cut-neighbourly k₁ k₂ wf₁ wf₂ x k₂≤k₁ =
    cut k₂ wf₂ (x ⊩ k₂)                                ≡˘⟨ cong (cut k₂ wf₂) (x .neighbourly k₁ k₂ k₂≤k₁) ⟩
    cut k₂ wf₂ (x ⊩ k₁ ⊢ k₂)                           ≡˘⟨ W-comp-eq _ _ (x ⊩ k₁) ⟩
    W[ [ cut-alg k₂ wf₂ ]W-hom W∘ k₂ ⊣-alg ]↓ (x ⊩ k₁) ≡⟨ cong (flip W[_]↓ (x ⊩ k₁)) (W⟶-≡ _ _ (cut-com k₁ k₂ wf₁ wf₂ k₂≤k₁) (λ _ _ → refl) refl) ⟩
    W[ [ k₂ ⊣-alg ]W-hom W∘ cut-alg k₁ wf₁ ]↓ (x ⊩ k₁) ≡⟨ W-comp-eq _ _ (x ⊩ k₁) ⟩
    cut k₁ wf₁ (x ⊩ k₁) ⊢ k₂ ∎

  solve : X → Neighbours A
  solve x ⊩ w = find w (well-founded (s , s≢ε) w) x
  solve x .neighbourly v w v≥w = find-neighbourly v w (well-founded (s , s≢ε) v) (well-founded (s , s≢ε) w) x v≥w

module _ (s : W) (s≢ε : s ≢ ε) {X A : Type} where
  open Solve {X = X} {A = A} s s≢ε

  solve-disp : (X → INeighbours (X ⊎ A) ⊎ A) → X → Neighbours A
  solve-disp =
\end{code}
%<*solve>
\begin{code}
    solve ⦂ (X → INeighbours (X ⊎ A) ⊎ A) →′ X →′ Neighbours A
\end{code}
%</solve>

