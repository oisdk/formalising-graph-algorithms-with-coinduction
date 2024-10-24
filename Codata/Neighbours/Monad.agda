{-# OPTIONS --safe --lossy-unification #-}

open import Prelude renaming ([_] to [_]⊩)
open import Algebra
open import Algebra.Monus

module Codata.Neighbours.Monad
  {W : Type} (mon : WellFoundedMonus W)
  where

open import Codata.Neighbours mon

open WellFoundedMonus mon

open Weight (weight W tapom)

open import Data.Weighted ⊕-semigroup hiding (⟪_⟫)
-- open import Data.Weighted.Monad (weight W tapom)
--   renaming (return to ηʷ) hiding (_>>=_)
import Data.Weighted.Monad (weight _ tapom) as WB

open WB using (wmap; _⋊_)
open import Data.Weighted.Functor
open import Data.Weighted.Cutoff totalOrder
open import Data.Weighted.CutoffMonus tmapom
open import Path.Reasoning


module NeighboursFunctor where
  map : (A → B) → Neighbours A → Neighbours B
  map = mapₙ

  map-id : (xs : Neighbours A) → map id xs ≡ xs
  map-id xs = search≡ λ w → WB.wmap-id (xs ⊩ w)

  map-comp : (f : B → C) (g : A → B) (x : Neighbours A) → map f (map g x) ≡ map (f ∘ g) x
  map-comp f g x = search≡ λ w → WB.wmap-comp f g (x ⊩ w)

neighboursFunctor : Functor Neighbours
neighboursFunctor = record { NeighboursFunctor }

_∘⊩_ : (A → Neighbours B) → W → A → Weighted B
(k ∘⊩ w) x = k x ⊩ w

module NeighboursMonad where
  _>>=_ : Neighbours A → (A → Neighbours B) → Neighbours B
  xs >>= k = μ (mapₙ k xs)

  >>=-lemma : ∀ (xs : Neighbours A) (k : A → Neighbours B) w → (xs >>= k) ⊩ w ≡ ((xs ⊩ w) WB.>>= (k ∘⊩ w)) ⊢ w
  >>=-lemma xs k w = 
    (xs >>= k) ⊩ w ≡⟨⟩
    wmap k (xs ⊩ w) ⊪ w ⊢ w ≡⟨ cong (_⊢ w) (WB.>>=-wmap k (_⊩ w) (xs ⊩ w)) ⟩
    ((xs ⊩ w) WB.>>= (k ∘⊩ w)) ⊢ w ∎

  _>=>_ : (A → Neighbours B) → (B → Neighbours C) → A → Neighbours C
  (xs >=> ys) v = xs v >>= ys

  return : A → Neighbours A
  return = η

  >>=-map : (f : A → B) (x : Neighbours A) → mapₙ f x ≡ x >>= (return ∘ f)
  >>=-map f x = search≡ λ w →
    mapₙ f x ⊩ w ≡⟨⟩
    wmap f (x ⊩ w) ≡˘⟨ cong (wmap f) (x .neighbourly w w ≤-refl) ⟩
    wmap f (x ⊩ w ⊢ w) ≡˘⟨ ⊢-wmap f (x ⊩ w) w ⟩
    wmap f (x ⊩ w) ⊢ w ≡⟨ cong (_⊢ w) (WB.wmap->>= f (x ⊩ w)) ⟩
    ((x ⊩ w) WB.>>= (WB.return ∘ f)) ⊢ w ≡⟨⟩
    ((x ⊩ w) WB.>>= ((return ∘ f) ∘⊩ w)) ⊢ w ≡˘⟨ >>=-lemma x (return ∘ f) w ⟩
    (x >>= (return ∘ f)) ⊩ w ∎

  >>=-idˡ : ∀  (k : A → Neighbours B) (x : A) → return x >>= k ≡ k x
  >>=-idˡ k x = search≡ λ w →
    ((ε ⋊ k x ⊩ w) ∪ ⟅⟆) ⊢ w ≡⟨ cong (_⊢ w) (∪-idʳ _ ; WB.ε⋊ _) ⟩
    k x ⊩ w ⊢ w ≡⟨ k x .neighbourly w w ≤-refl ⟩
    k x ⊩ w ∎

  >>=-idʳ : (x : Neighbours A) → x >>= return ≡ x
  >>=-idʳ x = search≡ λ w →
    (x >>= return) ⊩ w ≡⟨⟩
    μ (mapₙ η x) ⊩ w ≡⟨⟩
    mapₙ η x ⊩ w ⊪ w ⊢ w ≡⟨⟩
    wmap η (x ⊩ w) ⊪ w ⊢ w ≡⟨⟩
    (wmap η (x ⊩ w) WB.>>= λ x′ → x′ ⊩ w) ⊢ w ≡⟨ cong (_⊢ w) (WB.>>=-wmap η (_⊩ w) (x ⊩ w)) ⟩
    (x ⊩ w WB.>>= λ x′ → η x′ ⊩ w) ⊢ w ≡⟨⟩
    (x ⊩ w WB.>>= WB.return) ⊢ w ≡⟨ cong (_⊢ w) (WB.>>=-idʳ (x ⊩ w)) ⟩
    x ⊩ w ⊢ w ≡⟨ x .neighbourly w w ≤-refl ⟩
    x ⊩ w ∎

  >>=-assoc : (x : Neighbours A) (y : A → Neighbours B) (z : B → Neighbours C)
            → (x >>= y) >>= z ≡ x >>= (λ x′ → y x′ >>= z)
  >>=-assoc x y z = search≡ λ w →
    ((x >>= y) >>= z) ⊩ w ≡⟨⟩
    μ (mapₙ z (x >>= y)) ⊩ w ≡⟨⟩
    mapₙ z (x >>= y) ⊩ w ⊪ w ⊢ w ≡⟨⟩
    wmap z ((x >>= y) ⊩ w) ⊪ w ⊢ w ≡⟨⟩
    wmap z (wmap y (x ⊩ w) ⊪ w ⊢ w) ⊪ w ⊢ w ≡⟨ cong (_⊢ w) (WB.>>=-wmap z (_⊩ w) (wmap y (x ⊩ w) ⊪ w ⊢ w)) ⟩
    ((wmap y (x ⊩ w) ⊪ w ⊢ w) WB.>>= (λ x′ → z x′ ⊩ w)) ⊢ w ≡˘⟨ >>=-⊢ˡ w _ (λ x′ → z x′ ⊩ w)  ⟩
    ((wmap y (x ⊩ w) ⊪ w) WB.>>= (λ x′ → z x′ ⊩ w)) ⊢ w ≡⟨ cong (λ e → (e WB.>>= (λ x′ → z x′ ⊩ w)) ⊢ w) (WB.>>=-wmap y (_⊩ w) (x ⊩ w)) ⟩
    (((x ⊩ w) WB.>>= λ x′ → y x′ ⊩ w) WB.>>= (λ x′ → z x′ ⊩ w)) ⊢ w ≡⟨ cong (_⊢ w) (WB.>>=-assoc (x ⊩ w) (λ x′ → y x′ ⊩ w) (λ x′ → z x′ ⊩ w)) ⟩
    ((x ⊩ w) WB.>>= (λ x′ → (y x′ ⊩ w) WB.>>= (z ∘⊩ w))) ⊢ w ≡⟨ >>=-⊢ʳ w _ _ ⟩
    ((x ⊩ w) WB.>>= (λ x′ → ((y x′ ⊩ w) WB.>>= (z ∘⊩ w)) ⊢ w)) ⊢ w ≡˘⟨ cong (λ e → ((x ⊩ w) WB.>>= e) ⊢ w) (funExt λ x → >>=-lemma (y x) z w) ⟩
    ((x ⊩ w) WB.>>= (λ x′ → (y x′ >>= z) ⊩ w)) ⊢ w ≡˘⟨ cong (_⊢ w) (WB.>>=-wmap (y >=> z) (_⊩ w) (x ⊩ w)) ⟩
    wmap (λ x′ → y x′ >>= z) (x ⊩ w) ⊪ w ⊢ w ≡⟨⟩
    (x >>= (λ x′ → y x′ >>= z)) ⊩ w ∎

neighboursMonad : Monad Neighbours
neighboursMonad = record { NeighboursMonad }

module NeighboursComMonadPlus where
  open NeighboursMonad

  monad : Monad Neighbours
  monad = neighboursMonad

  empty : Neighbours A
  empty ⊩ w = ⟅⟆
  empty .neighbourly w v w≥v = refl

  _<|>_ : Neighbours A → Neighbours A → Neighbours A
  (x <|> y) ⊩ w = x ⊩ w ∪ y ⊩ w
  (x <|> y) .neighbourly w v w≥v = ⊢-∪ (x ⊩ w) (y ⊩ w) v ; cong₂ _∪_ (x .neighbourly w v w≥v) (y .neighbourly w v w≥v)

  <|>-idˡ : (x : Neighbours A) → empty <|> x ≡ x
  <|>-idˡ x = search≡ λ w → refl

  <|>-assoc : (x y z : Neighbours A) → (x <|> y) <|> z ≡ x <|> (y <|> z)
  <|>-assoc x y z = search≡ λ w → ∪-assoc (x ⊩ w) (y ⊩ w) (z ⊩ w) 

  <|>-com : (x y : Neighbours A) → x <|> y ≡ y <|> x
  <|>-com x y = search≡ λ w → ∪-com (x ⊩ w) (y ⊩ w)

  >>=-annˡ : (x : A → Neighbours B) → (empty >>= x) ≡ empty
  >>=-annˡ x = search≡ λ w →
    (empty >>= x) ⊩ w ≡⟨ >>=-lemma empty x w  ⟩
    ((empty ⊩ w) WB.>>= (x ∘⊩ w)) ⊢ w ≡⟨⟩
    ⟅⟆ ∎

  >>=-annʳ : (x : Neighbours A) → (x >>= const empty) ≡ empty {A = B}
  >>=-annʳ x = search≡ λ w →
    (x >>= const empty) ⊩ w ≡⟨ >>=-lemma x (const empty) w ⟩
    ((x ⊩ w) WB.>>= const empty ∘⊩ w) ⊢ w ≡⟨⟩
    ((x ⊩ w) WB.>>= const ⟅⟆) ⊢ w ≡⟨ cong (_⊢ w) (WB.>>=-⟅⟆ (x ⊩ w) ) ⟩
    ⟅⟆ ≡⟨⟩
    empty ⊩ w ∎ 

  <|>-distribˡ : (x y : Neighbours A) → (z : A → Neighbours B) → ((x <|> y) >>= z) ≡ (x >>= z) <|> (y >>= z)
  <|>-distribˡ x y z = search≡ λ w → 
    ((x <|> y) >>= z) ⊩ w ≡⟨ >>=-lemma (x <|> y) z w ⟩
    (((x <|> y) ⊩ w) WB.>>= z ∘⊩ w) ⊢ w ≡⟨⟩
    ((x ⊩ w ∪ y ⊩ w) WB.>>= z ∘⊩ w) ⊢ w ≡⟨ cong (_⊢ w) (WB.>>=-∪ (x ⊩ w) (y ⊩ w) (z ∘⊩ w)) ⟩
    (((x ⊩ w) WB.>>= z ∘⊩ w) ∪ ((y ⊩ w) WB.>>= z ∘⊩ w)) ⊢ w ≡⟨ ⊢-∪ ((x ⊩ w) WB.>>= z ∘⊩ w) ((y ⊩ w) WB.>>= z ∘⊩ w) w  ⟩
    ((x ⊩ w) WB.>>= z ∘⊩ w) ⊢ w ∪ ((y ⊩ w) WB.>>= z ∘⊩ w) ⊢ w ≡˘⟨ cong₂ _∪_ (>>=-lemma x z w) (>>=-lemma y z w) ⟩
    ((x >>= z) ⊩ w ∪ (y >>= z) ⊩ w) ≡⟨⟩
    ((x >>= z) <|> (y >>= z)) ⊩ w ∎

  <|>-distribʳ : (x : Neighbours A) → (y z : A → Neighbours B) → (x >>= (λ x′ → y x′ <|> z x′)) ≡ (x >>= y) <|> (x >>= z)
  <|>-distribʳ x y z = search≡ λ w → 
    (x >>= (λ x′ → y x′ <|> z x′)) ⊩ w ≡⟨ >>=-lemma x _ w ⟩
    ((x ⊩ w) WB.>>= (λ x′ → y x′ <|> z x′) ∘⊩ w) ⊢ w ≡⟨⟩
    ((x ⊩ w) WB.>>= (λ x′ → y x′ ⊩ w ∪ z x′ ⊩ w)) ⊢ w ≡⟨ cong (_⊢ w) (WB.=<<-∪ (x ⊩ w) _ _) ⟩
    (((x ⊩ w) WB.>>= (y ∘⊩ w)) ∪ ((x ⊩ w) WB.>>= (z ∘⊩ w))) ⊢ w ≡⟨ ⊢-∪ _ _ w ⟩
    ((x ⊩ w) WB.>>= (y ∘⊩ w)) ⊢ w ∪ ((x ⊩ w) WB.>>= (z ∘⊩ w)) ⊢ w ≡˘⟨ cong₂ _∪_ (>>=-lemma x y w) (>>=-lemma x z w) ⟩
    (x >>= y) ⊩ w ∪ (x >>= z) ⊩ w ≡⟨⟩
    ((x >>= y) <|> (x >>= z)) ⊩ w ∎

neighboursMonadPlus : ComMonadPlus Neighbours
neighboursMonadPlus = record {  NeighboursComMonadPlus }
