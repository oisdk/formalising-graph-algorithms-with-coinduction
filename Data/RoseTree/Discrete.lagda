\begin{code}
open import Prelude

module Data.RoseTree.Discrete {c} {C : Type c} (disc : Discrete C) where

private
  infix 4 _≟_
  _≟_ = disc

open import Data.RoseTree

\end{code}
%<*insert-trie>
\begin{code}
insert-trie : List C → Forest C → Forest C
insert-trie = foldr ins id
  where
  ins : C → (Forest C → Forest C) → Forest C → Forest C
  ins x k [] = (x & k []) ∷ []
  ins x k ((y & ys) ∷ xs) =
    if does (x ≟ y)
      then (y & k ys) ∷ xs
      else (y & ys) ∷ ins x k xs
\end{code}
%</insert-trie>
%<*rose-trie>
\begin{code}
rose-trie : List (List C) → Forest C
rose-trie = foldr insert-trie []
\end{code}
%</rose-trie>
\begin{code}

un-forest : Forest C → List (List C)
un-forest = fold-forest (λ x xs → mapl (x ∷_) xs) _++_ []

un-trie : Tree C → List (List C)
un-trie = fold-tree (λ x xs → mapl (x ∷_) xs) _++_ []

-- un-trie-inv : ∀ x → rose-trie (un-forest x) ≡ x
-- un-trie-inv [] = refl
-- un-trie-inv ((x & xs) ∷ xss) =
--   rose-trie (un-forest ((x & xs) ∷ xss)) ≡⟨⟩
--   rose-trie (un-trie (x & xs) ++ un-forest xss) ≡⟨ {!!} ⟩
--   foldr insert-trie (rose-trie (un-forest xss)) (un-trie (x & xs)) ≡⟨ {!!} ⟩
--   foldr insert-trie xss (un-trie (x & xs)) ≡⟨⟩
--   foldr insert-trie xss (mapl (x ∷_) (un-forest xs)) ≡⟨ {!!} ⟩
--   foldr (insert-trie ∘ (x ∷_)) xss (un-forest xs) ≡⟨ {!!} ⟩
--   (x & xs) ∷ xss ∎
\end{code}
