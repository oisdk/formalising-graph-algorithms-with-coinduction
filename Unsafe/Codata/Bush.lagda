\begin{code}
open import Prelude
open import Algebra
open import Algebra.Monus

module Unsafe.Codata.Bush {W : Type} (mon : WellFoundedMonus W) where

open import Codata.Bush mon
open WellFoundedMonus mon

postulate
\end{code}
%<*join-alg>
\begin{code}
  join-alg : Forest (Bush A) → Bush A
\end{code}
%</join-alg>
%<*join-coh>
\begin{code}
  join-coh :  (x y : Forest (Bush A)) →
              Equiv-UpTo x y →
              join-alg x ≡ join-alg y
\end{code}
%</join-coh>
%<*join-hole>
\begin{code}
join : Bush (Bush A) → Bush A
join = rec/ squash/ join-alg join-coh
\end{code}
%</join-hole>
