\begin{code}
open import Prelude hiding (a; b; c; [_])
open import Algebra
open import Algebra.Monus

module Unsafe.Codata.Forest where

open import Data.Nat.Monus
open TMAPOM nat-mon
open Weight (weight ℕ tapom)

open import Data.Vert
open import Unsafe.Codata.Inf
open import Unsafe.Codata.Fix
open import Data.Weighted ⊕-semigroup hiding (⟪_⟫)
open import Data.Weighted.Monad
  (weight ℕ tapom)
  renaming (_>>=_ to _>>=′_; return to return′)
open import Data.Weighted.Syntax ⊕-semigroup

W : Type
W = ℕ

private module UnquotientedForest where
  Forest : Type → Type
\end{code}
%<*unquot-forest-def>
\begin{code}
  Forest = List ∘ ((W ×_) ∘ List) ∞
\end{code}
%</unquot-forest-def>
\begin{code}

Forest : Type → Type
\end{code}
%<*forest-def>
\begin{code}[number=forest-def]
Forest = Weighted ∘ Weighted ∞
\end{code}
%</forest-def>
\begin{code}
{-# TERMINATING #-}
_>>=_ : Forest A → (A → Forest B) → Forest B
xs >>= k = xs >>=′ ((return′ ∘ ⟪_⟫ ∘ inl ∘ (_>>= k) ▿ k) ∘ out)

xs : Forest Vert
\end{code}
%<*xs>
\begin{code}
xs =  ⟅ 7  ▹ ⟪ inl  ⟅  1  ▹ ⟪ inr a ⟫ 
                    ,  2  ▹ ⟪ inr b ⟫ ⟆ ⟫
      , 3  ▹ ⟪ inr c ⟫ ⟆
\end{code}
%</xs>
\begin{code}
k : Vert → Forest ℕ
\end{code}
%<*k>
\begin{code}
k = λ  { b  →  ⟅  3  ▹ ⟪ inr 0 ⟫ ⟆
       ; c  →  ⟅  5  ▹ ⟪ inr 1 ⟫
               ,  6  ▹ ⟪ inr 2 ⟫ ⟆
       ; _  →  ⟅⟆ }
\end{code}
%</k>
\begin{code}
_ :
\end{code}
%<*res>
\begin{code}
  xs >>= k ≡  ⟅  7  ▹ ⟪ inl ⟅ 5 ▹ ⟪ inr 0 ⟫ ⟆ ⟫ ,  8  ▹ ⟪ inr 1 ⟫ ,  9  ▹ ⟪ inr 2 ⟫ ⟆
\end{code}
%</res>
\begin{code}
_ = refl

GraphOf : Type → Type
GraphOf A = A → Forest A

IForest : Type → Type
\end{code}
%<*iforest>
\begin{code}
IForest = Weighted ∘ Forest
\end{code}
%</iforest>
\end{code}
%<*delay>
\begin{code}
delay : GraphOf A → A → IForest A
delay g = return ∘ g 
\end{code}
%</delay>
\begin{code}
  where return = return′

return : A → Forest A
return = return′ ∘ ⟪_⟫ ∘ inr

Weighted[_] : (A → B) → Weighted A → Weighted B
Weighted[ f ] xs = xs >>=′ (return′ ∘ f)
\end{code}
%<*sigma>
\begin{code}
σ : IForest A → Forest A
σ = Weighted[ ⟪_⟫ ∘ inl ]
\end{code}
%</sigma>
%<*dfs-e>
\begin{code}
dfsₑ : GraphOf A → A → Forest (A ⊎ A)
dfsₑ g x =
  return (inr x) ∪ (g x >>= λ y → return (inl y))
\end{code}
%</dfs-e>
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
%<*dfs>
\begin{code}
dfs : GraphOf A → A → Forest A
dfs g x =
  return x ∪ (g x >>= λ y → dfs g y)
\end{code}
%</dfs>
\begin{code}
\end{code}
%<*dfs-g>
\begin{code}
dfsⱼ : (A → IForest A) → A → Forest (IForest A ⊎ A)
dfsⱼ g x = return (inr x) ∪ return (inl (g x))
\end{code}
%</dfs-g>
\begin{code}
private variable X : Type
\end{code}
%<*verts-eqn>
\begin{code}
verts : X → IForest (X ⊎ Vert) ⊎ Vert
verts x = inl  ⟅  1  ▹ return (inr  a)
               ,  2  ▹ return (inl  x) ⟆
\end{code}
%</verts-eqn>
\begin{code}
⋯ : Weighted A
⋯ = ⟅⟆

soln : Forest Vert
\end{code}
%<*solution>
\begin{code}
soln =  ⟅  1  ▹ ⟪ inl  ⟅  0  ▹ ⟪ inr a ⟫ ⟆ ⟫
        ,  2  ▹ ⟪ inl  ⟅  1  ▹ ⟪ inl  ⟅  0  ▹ ⟪ inr a ⟫ ⟆ ⟫
                       ,  2  ▹ ⟪ inl  ⋯ ⟫ ⟆ ⟫ ⟆
\end{code}
%</solution>
\begin{code}
g₁ : GraphOf Vert
\end{code}
%<*g1>
\begin{code}
g₁ a =  ⟅ 2 ▹ ⟪ inr b ⟫ ⟆
\end{code}
%</g1>
\begin{code}
g₁ _ = ⟅⟆

g₂ : GraphOf Vert
\end{code}
%<*g2>
\begin{code}
g₂ a = ⟅ 1 ▹ ⟪ inl  ⟅ 1 ▹ ⟪ inr b ⟫ ⟆ ⟫ ⟆
\end{code}
%</g2>
\begin{code}
g₂ _ = ⟅⟆
\end{code}
