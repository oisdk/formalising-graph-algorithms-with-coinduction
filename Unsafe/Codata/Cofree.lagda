\begin{code}
{-# OPTIONS --no-positivity-check --no-termination-check #-}

module Unsafe.Codata.Cofree where

open import Prelude hiding (a; b; c; [_]; acc; _+_)
open import Data.Weighted.Functor
open import Unsafe.Codata.Fix
open import Data.Vert

Cofree : (Type → Type) → Type → Type
\end{code}
%<*def>
\begin{code}[number=cofree-def]
Cofree F A = ν X ． A × F X
\end{code}
%</def>
\begin{code}
open import Algebra

private variable F : Type → Type

extract : Cofree F A → A
extract = fst ∘ out

unwrap : Cofree F A → F (Cofree F A) 
unwrap = snd ∘ out

private module CofreeCons where
\end{code}
%<*cofree-cons>
\begin{code}
  _◂_ : A → F (Cofree F A) → Cofree F A
\end{code}
%</cofree-cons>
\begin{code}
  out (x ◂ xs) = x , xs

infixr 5 _◂_
pattern _◂_ x xs = ⟪ x , xs ⟫

cong-◂ : {x y : Cofree F A} → (extract x ≡ extract y) → (unwrap x ≡ unwrap y) → x ≡ y
cong-◂ p ps i .out .fst = p i
cong-◂ p ps i .out .snd = ps i
module FuncImpls { F : Type → Type } ⦃ func : Functor F ⦄ where
  open Functor func

  instance
    func-∝ : Functor (λ X → B × F X)
    func-∝ .Functor.map f (x , y) = x , map f y
    func-∝ .Functor.map-id (x , y) = cong (x ,_) (map-id y)
    func-∝ .Functor.map-comp f g (x , y) = cong (x ,_) (map-comp f g y)
\end{code}
%<*trace>
\begin{code}
  trace : (A → F A) → A → Cofree F A
  trace ψ = ana (λ x → x , ψ x)
\end{code}
%</trace>
\begin{code}
open import Algebra.Monus
module Weighted where
  𝑆 : Type
  𝑆 = ℕ

  open import Data.Nat.Monus

  open TMAPOM nat-mon

  open Weight (weight _ tapom)

  open import WeightedGraphs nat-mon
  open import WeightedGraphs.Nat

  open import Data.Weighted ⊕-semigroup
  open import Data.Weighted.Monad (weight _ tapom) using (functorWeighted)
  
  instance
    functorWeighted′ : Functor {ℓ₁ = ℓzero} Weighted
    functorWeighted′ = functorWeighted

  open Functor ⦃ ... ⦄

  Tree : Type → Type
\end{code}
%<*tree>
\begin{code}
  Tree = Cofree Weighted
\end{code}
%</tree>
\begin{code}
  Heap : Type → Type
\end{code}
%<*heap-def>
\begin{code}[number=heap-def]
  Heap = Cofree (List ∘ (𝑆 ×_))
\end{code}
%</heap-def>
\begin{code}
  private module TraceTree where
\end{code}
%<*trace-ty-2>
\begin{code}
    trace : GraphOf A → A → Tree A
\end{code}
%</trace-ty-2>
\begin{code}
    trace = FuncImpls.trace

  open FuncImpls public

  private module ReifyExamples where

    open import Data.Weighted.Syntax ⊕-semigroup
    ⋯ : _
    ⋯ = unwrap (trace graph b)

    _ :
\end{code}
%<*trace-wtree>
\begin{code}[number=trace-wtree]
        trace graph a ≡
          a ◂  ⟅  7  ▹ b  ◂  ⟅  1  ▹ c  ◂ ⟅ 3  ▹ d  ◂ ⟅ 5 ▹ b ◂ ⋯ ⟆ ,  1  ▹ b  ◂ ⋯  ⟆                 ⟆
               ,  2  ▹ c  ◂  ⟅  3  ▹ d  ◂ ⟅ 5  ▹ b  ◂ ⋯                             ⟆ ,  1  ▹ b  ◂ ⋯  ⟆ ⟆
\end{code}
%</trace-wtree>
\begin{code}
    _ = cong-◂ refl
      (cong₂
        (7 ▹_∷_)
        (cong-◂ refl
          (cong₂
            (1 ▹_∷_)
            (cong-◂ refl
              (cong₂
                (3 ▹_∷_)
                (cong-◂ refl (cong₂ (5 ▹_∷_) (cong-◂ refl refl) refl))
                (cong₂ (1 ▹_∷_) (cong-◂ refl refl) refl)))
            refl))
        (cong₂ (2 ▹_∷_) (cong-◂ refl (cong₂ (3 ▹_∷_) (cong-◂ refl (cong₂ (5 ▹_∷_) (cong-◂ refl refl) refl))
        (cong₂ (1 ▹_∷_) (cong-◂ refl refl) refl))) refl))


    infixl 6 _+_
    _+_ = _∙_

    _ : Cofree Weighted Vert
    _ =
\end{code}
%<*trace-wtree-accum-2>
\begin{code}
          a ◂ ⟅  7  ▹ b  ◂  ⟅  8  ▹ c  ◂ ⟅ 11  ▹ d  ◂ ⋯ , 9 ▹ b ◂ ⋯  ⟆                ⟆
              ,  2  ▹ c  ◂  ⟅  5  ▹ d  ◂ ⟅ 10  ▹ b  ◂ ⋯              ⟆ , 3  ▹ b  ◂ ⋯  ⟆ ⟆
\end{code}
%</trace-wtree-accum-2>
\begin{code}
    _ = (refl { _ } { Tree Vert })
  open import Data.Link 𝑆
  open import Data.NonEmpty

  Chain : Type → Type
\end{code}
%<*chain>
\begin{code}
  Chain = Cofree Link
\end{code}
%</chain>
\begin{code}

  private module Result where
    open import Data.NonEmpty.Syntax
    ⋯ : Maybe A
    ⋯ = ⟨⟩

    result : Chain (List⁺ Vert)
    result = 
\end{code}
%<*result>
\begin{code}
      [ a ] ◂ 2 ∝ [ c , a ] ◂ 1 ∝ [ b , c , a ] ◂ 1 ∝ [ c , b , c , a ] ◂ 1 ∝ [ d , c , a ] ◂ ⋯
\end{code}
%</result>
\begin{code}
  module _ {F : Type → Type} ⦃ _ : Functor F ⦄ where

  postulate sorry : A

  merges-alg : Ψ[ xs ⦂ Weighted (Cofree Weighted A) ] ↦ Link (Cofree Weighted A)
  merges-alg .fst ⟅⟆ = ⟨⟩
  merges-alg .fst (w ▹ x ∷ _ ⟨ ⟨⟩ ⟩) = w ∝ x
  merges-alg .fst (w₁ ▹ x₁ ∷ _ ⟨ w₂ ∝ x₂ ⟩) with w₁ ≤|≥ w₂
  ... | inl (k , w₁≤w₂) = w₁ ∝ extract x₁ ◂ k ▹ x₂ ∷ unwrap x₁
  ... | inr (k , w₁≥w₂) = w₂ ∝ extract x₂ ◂ k ▹ x₁ ∷ unwrap x₂
  merges-alg .snd = sorry

  merges :  Weighted (Tree A) →
            Link (Tree A)
  merges = ⟦ merges-alg ⟧
\end{code}
%<*search-ty>
\begin{code}
  search : Tree A → Chain A
\end{code}
%</search-ty>
\begin{code}
  search = ana (extract ▵ merges ∘ unwrap)
\end{code}
