\begin{code}
{-# OPTIONS --safe #-}

module Data.RoseTree where

open import Prelude

infixr 4.5 _&_
mutual
  Forest : Type a → Type a
\end{code}
%<*forest-def>
\begin{code}
  Forest A = List (Tree A)
\end{code}
%</forest-def>
\begin{code}
  data Tree (A : Type a) : Type a
\end{code}
%<*tree-def>
\begin{code}
  data Tree A where _&_ : A → Forest A → Tree A
\end{code}
%</tree-def>
\begin{code}
open Tree public

module _
  (root : A → B → C)
  (branch : C → B → B)
  (leaf : B)
  where
  fold-tree : Tree A → C
  fold-forest : Forest A → B

  fold-tree (x & xs) = root x (fold-forest xs)

  fold-forest [] = leaf
  fold-forest (x ∷ xs) = branch (fold-tree x) (fold-forest xs)
\end{code}
