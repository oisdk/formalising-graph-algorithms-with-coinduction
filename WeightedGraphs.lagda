\begin{code}
{-# OPTIONS --safe --lossy-unification #-}

open import Prelude hiding (a; b; c; _∷_)
open import Algebra
open import Algebra.Monus

module WeightedGraphs {W : Type} (mon : TMAPOM W) where

open TMAPOM mon
open import Data.Weighted ⊓-semigroup
open import Data.Weighted.Monad (weight _ tapom)
open import Data.Weighted.Syntax ⊓-semigroup
open import Data.Vert

GraphOf : {a : Level} → Type a → Type a
\end{code}
%<*graph-of>
\begin{code}[number=eqn:weighted-graphof]
GraphOf V = V → Weighted V
\end{code}
%</graph-of>
%<*graph>
\begin{code}
Graph : Type₁
Graph = Σ[ V ⦂ Type ] × GraphOf V
\end{code}
%</graph>
\begin{code}

module _ {A : Type} where
  _ : GraphOf A
  _ =
\end{code}
%<*id-graph>
\begin{code}
   return ⦂ GraphOf A
\end{code}
%</id-graph>
%<*graph-overlay>
\begin{code}
_⊞_ :  GraphOf A →
       GraphOf A →
       GraphOf A
(f ⊞ g) v = f v ∪ g v
\end{code}
%</graph-overlay>
%<*graph-empty>
\begin{code}
empty : GraphOf A
empty _ = ⟅⟆
\end{code}
%</graph-empty>
%<*graph-connect>
\begin{code}
_>=>_ :  GraphOf A →
         GraphOf A →
         GraphOf A
\end{code}
%</graph-connect>
\begin{code}
(x >=> y) v = x v >>= y
\end{code}
%<*vplus>
\begin{code}
_+++_ :  GraphOf A →
         GraphOf B →
         GraphOf (A ⊎ B)
(g +++ h) =
  either  (wmap inl ∘ g)
          (wmap inr ∘ h)
\end{code}
%</vplus>
%<*vtimes>
\begin{code}
_***_ :  GraphOf A →
         GraphOf B →
         GraphOf (A × B)
(g *** h) (vₗ , vᵣ) = do
  x ← g vₗ
  y ← h vᵣ
  return (x , y)
\end{code}
%</vtimes>
\begin{code}
semiringGraph : Semiring (GraphOf A)
semiringGraph .Semiring._⊕_ = _⊞_
semiringGraph .Semiring._⊗_ = _>=>_
semiringGraph .Semiring.𝟙 = return
semiringGraph .Semiring.𝟘 = empty
semiringGraph .Semiring.⊕-assoc x y z = funExt λ v → ∪-assoc (x v) (y v) (z v)
semiringGraph .Semiring.⊗-assoc x y z = funExt λ v → >>=-assoc (x v) y z
semiringGraph .Semiring.𝟘⊕ _ = refl
semiringGraph .Semiring.⊕-com x y = funExt λ v → ∪-com (x v) (y v)
semiringGraph .Semiring.𝟙⊗ x = funExt λ v → >>=-idˡ v x
semiringGraph .Semiring.⊗𝟙 x = funExt λ v → >>=-idʳ (x v)
semiringGraph .Semiring.𝟘⊗ _ = refl
semiringGraph .Semiring.⊗𝟘 x = funExt λ v → >>=-⟅⟆ (x v)
semiringGraph .Semiring.⟨⊕⟩⊗ x y z = funExt λ v → >>=-∪ (x v) (y v) z
semiringGraph .Semiring.⊗⟨⊕⟩ x y z = funExt λ v → =<<-∪ (x v) y z

module SemiringInst {a : Level} {A : Type a} where
  open Semiring (semiringGraph {A = A}) public
open SemiringInst public

\end{code}
%<*unit>
\begin{code}
unit : Graph
unit = ⊤ , return
\end{code}
%</unit>
%<*void>
\begin{code}
void : Graph
void = ⊥ , absurd
\end{code}
%</void>
\begin{code}
_***′_ : Graph → Graph → Graph
(g ***′ h) .fst = g .fst × h .fst
(g ***′ h) .snd = g .snd *** h .snd

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Foundations.Everything hiding (_$_; _∘_; id; uncurry; _∎; step-≡; _≡⟨⟩_)

i*** : GraphOf A → GraphOf (B × A)
i*** xs (x , y) = wmap (x ,_) (xs y)

return-*** : ∀ (g : GraphOf A) → (return {A = B} *** g) ≡ i*** g
return-*** g = funExt (λ { (x , y) → >>=-idˡ x (λ x′ → g y >>= return ∘ (x′ ,_)) ; sym (wmap->>= (x ,_) (g y)) })

open import Data.Weighted.Functor

isoTransp  : (f : Iso A B) (x : A) → f .fun x ≡ transport (isoToPath f) x
isoTransp f x = sym (transportRefl _)

isoTransp⁻ : (f : Iso A B) (x : B) → f .inv x ≡ transport (sym (isoToPath f)) x
isoTransp⁻ f x = cong (f .inv) (sym (transportRefl _))

***-idˡ : ∀ g → unit ***′ g ≡ g
***-idˡ g = ΣPathTransport→PathΣ (unit ***′ g) g
  (isoToPath lUnit×Iso , funExt λ v →  cong (λ e → transport (λ i → GraphOf (isoToPath (lUnit×Iso {A = g .fst}) i)) e v) (return-*** (g .snd))
  ; cong′ {A = GraphOf (g .fst) } {x = transport (λ i → GraphOf (eg i)) (i*** (g .snd)) } {y = wmap id ∘ snd g} {B = Weighted (g .fst)}  (_$ v)
  (funExt lemma)
  ; wmap-id (snd g v)
  )
  where
  ig : (⊤ × g .fst) ⇔ g .fst
  ig = lUnit×Iso

  eg : (⊤ × g .fst) ≡ g .fst
  eg = isoToPath ig

  lemma′ : ∀ xs → subst Weighted eg (wmap (tt ,_) xs) ≡ wmap id xs
  lemma′ = ⟦ alg ⟧
    where
    alg : Ψ[ xs ⦂ Weighted (g .fst) ] ↦ subst Weighted eg (wmap (tt ,_) xs) ≡ wmap id xs
    alg .snd = eq-coh
    alg .fst ⟅⟆ = refl
    alg .fst (w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong₃ (_▹_∷_) (transportRefl w) (sym (isoTransp ig (tt , x))) refl ; cong (w ▹ x ∷_) P⟨xs⟩

  lemma : ∀ x → subst Weighted (eg) (i***  (g .snd) (subst id (sym eg) x)) ≡ wmap id (g .snd x)
  lemma x =
    subst Weighted eg (i***  (g .snd) (subst id (sym eg) x)) ≡⟨⟩
    subst Weighted eg (i***  (g .snd) (transport (sym eg) x)) ≡⟨ cong (λ e → subst Weighted eg (i*** (g .snd) e)) (sym (isoTransp⁻ ig x)) ⟩
    subst Weighted eg (i***  (g .snd) (ig .inv x)) ≡⟨⟩
    subst Weighted eg (i***  (g .snd) (tt , x)) ≡⟨⟩
    subst Weighted eg (wmap (tt ,_)  (g .snd x)) ≡⟨ lemma′ (g .snd x) ⟩
    wmap id (g .snd x) ∎
  

\end{code}
