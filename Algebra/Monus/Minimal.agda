{-# OPTIONS --safe #-}

open import Prelude
open import Algebra.Monus

module Algebra.Monus.Minimal
  {S : Type}
  (mon : WellFoundedMonus S)
  where

open WellFoundedMonus mon

infixr 8 _^_
_^_ : S → ℕ → S
x ^ zero  = ε
x ^ suc n = x ∙ (x ^ n)

module _ (o : S) (o≢ε : o ≢ ε) (o≤ : ∀ x → x ≡ ε ⊎ o ≤ x) where
  decomp : ∀ x → Acc [ o ]_≺_ x → ∃ n × x ≡ o ^ n
  decomp x wf with o≤ x 
  decomp x _        | inl x≡ε = zero , x≡ε
  decomp x (acc wf) | inr (k , x≡o∙k) =
    let n , p = decomp k (wf k (ε , (x≡o∙k ; comm o k ; sym (∙ε _))))
    in suc n , (x≡o∙k ; cong (o ∙_) p)

  generated : ∀ x → ∃ n × x ≡ o ^ n
  generated x = decomp x (well-founded (o , o≢ε) x)
