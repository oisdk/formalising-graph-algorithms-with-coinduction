\begin{code}
module Unsafe.Codata.Resumption where

open import Prelude
open import Unsafe.Codata.Inf

Res : (Type → Type) → (Type → Type) → Type → Type _
\end{code}
%<*resumption-def>
\begin{code}
Res Σ M = M ∘ (Σ ∘ M) ∞
\end{code}
%</resumption-def>
