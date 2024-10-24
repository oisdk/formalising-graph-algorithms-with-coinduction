\begin{code}
{-# OPTIONS --no-positivity-check --no-termination-check #-}

module Unsafe.Codata.Fix where

open import Prelude hiding ([_])

private module Defs where
  module AsFunc where
\end{code}
%<*nu-type>
\begin{code}
    ν : (Type → Type) → Type
\end{code}
%</nu-type>
\begin{code}
    ν _ = ⊤

  record ν (F : Type → Type) : Type where
    coinductive; constructor outᵒ
    field out′ : F (ν F)

  module _ {F : Type → Type} where
\end{code}
%<*delay>
\begin{code}
    ⟪_⟫ : F (ν F) → ν F
\end{code}
%</delay>
%<*out>
\begin{code}
    out : ν F → F (ν F)
\end{code}
%</out>
\begin{code}
    ⟪_⟫ = outᵒ
    out = ν.out′

infixr 0 ν
record ν (F : Type a → Type a) : Type a where
  coinductive; constructor ⟪_⟫
  field out : F (ν F)

syntax ν (λ x → e) = ν x ． e

open ν public

private
  variable
    F : Type a → Type a
    G : Type b → Type b


open import Algebra
module _ where
  open Functor ⦃ ... ⦄

  _[_]_ : (F : Type a → Type a) → ⦃ _ : Functor F ⦄ → (A → B) → F A → F B
  F [ f ] xs = map f xs

  module _ {F : Type a → Type a} ⦃ fnc : Functor F ⦄ where
\end{code}
%<*corec>
\begin{code}[number=ana]
    ana : (A → F A) → A → ν F
    out (ana ϕ r) = F [ ana ϕ ] (ϕ r)
\end{code}
%</corec>
\begin{code}
mana  :  (∀ {X} → (A → X) → A → F X)
      →   A → ν F
out (mana ϕ r) = ϕ (mana ϕ) r

νmap : (F (ν F) → G (ν G)) → ν F → ν G
νmap f xs = ⟪ f (xs .out) ⟫
\end{code}
