\begin{code}
{-# OPTIONS --safe --lossy-unification #-}

open import Prelude renaming ([_] to [_]⊩)
open import Algebra
open import Algebra.Monus

module Codata.Neighbours.Solves
  {W : Type} (mon : WellFoundedMonus W)
  (s : W)
  (s≢ε : s ≢ WellFoundedMonus.ε mon)
  where

open WellFoundedMonus mon

open Weight (weight W tapom)

open import Data.Weighted ⊕-semigroup hiding (⟪_⟫)
open import Data.Weighted.Monad (weight W tapom)
  using
    ( _⋊_
    ; bind-alg
    ; wmap-alg
    ; ⋊-alg
    ; wmap
    )
  renaming (return to ηʷ)
import Data.Weighted.Monad (weight _ tapom) as WB
open import Data.Weighted.Functor
open import Data.Weighted.Cutoff totalOrder
open import Data.Weighted.CutoffMonus tmapom

open import Path.Reasoning

open import Codata.Neighbours mon

module Solution {X : Type} (eᵢ : (X → INeighbours (X ⊎ A) ⊎ A)) where
  σ : INeighbours B → Neighbours B
  σ = _⋊ₙ_ s
 
  open Solve s s≢ε eᵢ

  cut-to-<s : ∀ w wf p x → w < p ∙ s → cut-to w wf p x ≡ ⟅⟆
  cut-to-<s w wf p x w<p∙s with p ∙ s ≤? w
  ... | no p∙s≰w = refl
  ... | yes p∙s≤w = absurd (w<p∙s p∙s≤w)

  cut-<s : ∀ w wf → w < s → ∀ x → cut w wf x ≡ ⟅⟆
  cut-<s w wf w<s = ⟦ alg ⟧
    where
    alg : Ψ[ x ⦂ Weighted (X ⊎ A) ] ↦ cut w wf x ≡ ⟅⟆
    alg .snd = eq-coh
    alg .fst ⟅⟆ = refl
    alg .fst (p ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong₂ _∪_ (cut-to-<s w wf p x ≲[ <[ w<s ] ≲; ≤[ x≤x∙y ] ≲; ≡[ comm s p ] ]) P⟨xs⟩

  soln-step : ∀ w wf p v
            → (p≺w : p ≺ₛ w)
            → step w p p≺w wf v ≡ (solve ▿ η) v ⊩ p≺w .fst
  soln-step w wf       p (inr x) _   = refl
  soln-step w (acc wf) p (inl x) p≺w = cong (λ e → find (p≺w .fst) e x) (isPropAcc _ _)

  soln-cut-to : ∀ w wf p v → (p≺w : p ≺ₛ w) → cut-to w wf p v ≡ s ∙ p ⋊ (solve ▿ η) v ⊩ p≺w .fst
  soln-cut-to w wf p v p≺w₁ with p ∙ s ≤? w
  ... | no  p⊀w = absurd (p⊀w p≺w₁)
  ... | yes p≺w₂ =
    p ∙ s ⋊ step w p p≺w₂ wf v        ≡⟨ cong (_⋊ step w p p≺w₂ wf v) (comm p s) ⟩
    s ∙ p ⋊ step w p p≺w₂ wf v        ≡⟨ cong (s ∙ p ⋊_) (soln-step w wf p v p≺w₂)  ⟩
    s ∙ p ⋊ (solve ▿ η) v ⊩ p≺w₂ .fst ≡⟨ cong (λ e → s ∙ p ⋊ (solve ▿ η) v ⊩ e) (cancelˡ (p ∙ s) _ _ (sym (p≺w₂ .snd) ; p≺w₁ .snd)) ⟩
    s ∙ p ⋊ (solve ▿ η) v ⊩ p≺w₁ .fst ∎

  soln-compd : ∀ k w wf → w ≡ s ∙ k → ∀ p v → cut-to w wf p v ≡ W[ [ w ⊣-alg ]W-hom W∘ bind-alg (_⊩ w) W∘ wmap-alg (solve ▿ η) W∘ ⋊-alg s ]↓ (k / p ▹ v)
  soln-compd k w wf w≡s∙k p v with p ≤? k
  ... | no p≰k = cut-to-<s w wf p v ≲[ ≡[ w≡s∙k ] ≲; <[ <-congˡ s p≰k ] ≲; ≡[ comm s p ] ]
  ... | yes (k₂ , k≡p∙k₂) =
    cut-to w wf p v                                                                     ≡⟨ soln-cut-to w wf p v (k₂ , (w≡s∙k ; cong (s ∙_) k≡p∙k₂ ; sym (assoc s p k₂) ; cong (_∙ k₂) (comm s p))) ⟩
    s ∙ p ⋊ (solve ▿ η) v ⊩ k₂                                                          ≡˘⟨ cong (s ∙ p ⋊_) (neighbourly ((solve ▿ η) v) w k₂ (p ∙ s , (w≡s∙k ; cong (s ∙_) k≡p∙k₂ ; sym (assoc s p k₂) ; cong (_∙ k₂) (comm s p) ; comm (p ∙ s) k₂))) ⟩
    s ∙ p ⋊ (solve ▿ η) v ⊩ w ⊢ k₂                                                      ≡˘⟨ ≤-⋊-⊢ (s ∙ p) ((solve ▿ η) v ⊩ w) w (k₂ , (w≡s∙k ; cong (s ∙_) k≡p∙k₂ ; sym (assoc s p k₂) )) ⟩
    (s ∙ p ⋊ (solve ▿ η) v ⊩ w) ⊢ w                                                     ≡⟨⟩
    W[ [ w ⊣-alg ]W-hom ]↓ (s ∙ p ⋊ (solve ▿ η) v ⊩ w)                                  ≡˘⟨ ∪-idʳ _ ⟩
    W[ [ w ⊣-alg ]W-hom W∘ bind-alg (_⊩ w) ]↓ (s ∙ p ▹ (solve ▿ η) v ∷ ⟅⟆)              ≡˘⟨ ∪-idʳ _ ⟩
    W[ [ w ⊣-alg ]W-hom W∘ bind-alg (_⊩ w) W∘ wmap-alg (solve ▿ η) ]↓ (s ∙ p ▹ v ∷ ⟅⟆)  ≡˘⟨ ∪-idʳ _ ⟩
    W[ [ w ⊣-alg ]W-hom W∘ bind-alg (_⊩ w) W∘ wmap-alg (solve ▿ η) W∘ ⋊-alg s ]↓ (p ▹ v ∷ ⟅⟆) ∎

  solution′ : ∀ x w wf → find w wf x ≡ (μ ∘ mapₙ (solve ▿ η) ∘ (σ ▿ η ∘ inr) ∘ eᵢ) x ⊩ w
  solution′ x w wf with eᵢ x
  ... | inr y = ηʷ y                 ≡˘⟨ return-⊢ y w ⟩
                ηʷ y ⊢ w             ≡˘⟨ cong (λ v → (v ▹ y ∷ ⟅⟆) ⊢ w) (ε∙ ε) ⟩
                (ε ∙ ε ▹ y ∷ ⟅⟆) ⊢ w ≡⟨⟩
                (μ ∘ mapₙ (solve ▿ η) ∘ (σ ▿ η ∘ inr)) (inr y) ⊩ w ∎
  ... | inl y with s ≤? w
  ... | no s≰w = cut-<s w wf s≰w (y ⊩ w)
  ... | yes (k , w≡s∙k) = 

    cut w wf (y ⊩ w)

      ≡⟨⟩

    [ cut-alg w wf ]W↓ (y ⊩ w)

      ≡⟨ cong (λ e → W[ e ]↓ (y ⊩ w))
        (W⟶-≡
          [ cut-alg w wf ]W-hom
          ([ w ⊣-alg ]W-hom W∘ bind-alg (_⊩ w) W∘ wmap-alg (solve ▿ η) W∘ ⋊-alg s W∘ k ⊣-alg)
          (soln-compd k w wf w≡s∙k)
          (λ _ _ → refl)
          refl) ⟩

    W[ [ w ⊣-alg ]W-hom W∘ bind-alg (_⊩ w) W∘ wmap-alg (solve ▿ η) W∘ ⋊-alg s W∘ k ⊣-alg ]↓ (y ⊩ w)

      ≡⟨ W-comp-eq _ (k ⊣-alg) (y ⊩ w)
       ; W-comp-eq _ (⋊-alg s) (y ⊩ w ⊢ k)
       ; W-comp-eq _ (wmap-alg (solve ▿ η)) (s ⋊ (y ⊩ w ⊢ k))
       ; W-comp-eq _ (bind-alg (_⊩ w)) (wmap (solve ▿ η) (s ⋊ (y ⊩ w ⊢ k)))
       ⟩

    wmap (solve ▿ η) (s ⋊ y ⊩ w ⊢ k) ⊪ w ⊢ w

      ≡⟨ cong (λ e → wmap (solve ▿ η) (s ⋊ e) ⊪ w ⊢ w) (neighbourly y w k (s , (w≡s∙k ; comm s k))) ⟩

    wmap (solve ▿ η) (s ⋊ y ⊩ k) ⊪ w ⊢ w ∎

  solution : ∀ x → solve x ≡ (μ ∘ mapₙ (solve ▿ η) ∘ (σ ▿ η ∘ inr) ∘ eᵢ) x
  solution x = search≡ (λ w → solution′ x w (well-founded (s , s≢ε) w))

module _ {X : Type} (eᵢ : (X → INeighbours (X ⊎ A) ⊎ A)) where
  open Solution eᵢ
  open Solve {X = X} {A = A} s s≢ε

  solution-disp :
\end{code}
%<*solution>
\begin{code}
    ∀ x → solve eᵢ x ≡ (μ ∘ mapₙ (solve eᵢ ▿ η) ∘ (σ ▿ η ∘ inr) ∘ eᵢ) x
\end{code}
%</solution>
\begin{code}
  solution-disp = solution

open import Codata.Neighbours.Monad mon
open NeighboursMonad using (>>=-map)
open Monad neighboursMonad
open Functor neighboursFunctor using (map-id)

open import Codata.CIM hiding (μ; η)

μ″ : Neighbours (Neighbours A) → Neighbours A
μ″ x = x >>= id

map″ : (A → B) → Neighbours A → Neighbours B
map″ f x = x >>= return ∘ f

μ-lemma : μ {A = A} ≡ μ″
μ-lemma = funExt (λ x → sym (cong μ (map-id x)))

map-lemma : (f : A → B) → mapₙ f ≡ map″ f
map-lemma f = funExt (>>=-map f)

module _ {X A : Type} where
  open Solve {X = X} {A = A} s s≢ε public
  open Solution  {A = A} {X = X} public

ideal : Ideal Neighbours INeighbours neighboursMonad neighboursFunctor
ideal .Ideal.mod .Module.μ′ = μ
ideal .Ideal.mod .Module.μ-η = funExt >>=-idʳ
ideal .Ideal.mod .Module.μ-μ = funExt (λ x → μ (μ x) ≡⟨ cong (_$ μ x) μ-lemma ; cong μ″ (cong (_$ x) μ-lemma) ; >>=-assoc x _ _ ⟩ μ (mapₙ (_>>= id) x) ∎)
ideal .Ideal.σ = _⋊ₙ_ s
ideal .Ideal.hom = funExt λ x → ( (s ⋊ₙ x) >>= id ) ≡⟨ sym (cong (_$ (s ⋊ₙ x)) μ-lemma) ; μ-⋊ s x ⟩ s ⋊ₙ (μ x) ∎ 
ideal .Ideal.natural f = funExt λ x →
  s ⋊ₙ mapₙ f x ≡⟨ mapₙ-⋊ₙ f s x ⟩
  mapₙ f (s ⋊ₙ x) ≡⟨ cong (_$ (s ⋊ₙ x)) (map-lemma f) ⟩
  mmap f (s ⋊ₙ x) ∎

cim : CIM Neighbours INeighbours neighboursMonad neighboursFunctor
cim .CIM.ideal = ideal
cim .CIM._‡ = solve
cim .CIM.solution eᵢ = funExt (solution eᵢ)
  ; cong₂ _∘_ μ-lemma (cong (_∘ (σ eᵢ ▿ η ∘ inr) ∘ eᵢ) (map-lemma (solve eᵢ ▿ η)))

open CIM cim

open ComMonadPlus neighboursMonadPlus

infixl 8 _∗
_∗ : (A → INeighbours A) → A → Neighbours A
g ∗ = e† λ v → η (inr v) <|> η (inl (g v))
\end{code}
