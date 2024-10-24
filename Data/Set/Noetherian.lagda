\begin{code}
{-# OPTIONS --safe #-}

open import Prelude

module Data.Set.Noetherian {a} {A : Type a} (disc : Discrete A) where

private
  infix 4 _≟_
  _≟_ = disc

open import Data.Set
open import Data.Set.Discrete disc
open import Data.Nat.Properties
open import Data.Nat

infixr 5 _#_
_#_ : A → 𝒦 A → ℕ
x # xs = if does (x ∈? xs) then 0 else 1

size : 𝒦 A → ℕ
size = ⟦ size-alg ⟧
  where
  opaque
    unfolding _∈?_
    lemma₁ : ∀ x y xs → (x # y ∷ xs) + (y # xs) ≡ (y # x ∷ xs) + (x # xs)
    lemma₁ x y xs with x ≟ y
    ... | yes x≡y = cong (_# xs) (sym x≡y) ; cong (_+ bool 1 0 (does (x ∈? xs))) (cong (bool 1 0 ∘ bool _ _) (sym (it-does (y ≟ x) (sym x≡y) )))
    ... | no  x≢y with x ∈? xs | y ∈? xs
    ... | no  x∉xs | y∈?xs = sym (+-comm (bool 1 0 (does y∈?xs)) 1) ; cong (_+ 1) (cong (bool 1 0 ∘ bool _ _) (sym (it-doesn't (y ≟ x) (x≢y ∘ sym))))
    ... | x∈?xs | no  y∉xs = +-comm (bool 1 0 (does x∈?xs)) 1 ; cong (_+ bool 1 0 (does x∈?xs)) (cong (bool 1 0 ∘ bool false true) (sym (it-doesn't (y ≟ x) (x≢y ∘ sym))))
    ... | yes x∈xs | yes y∈xs = cong (_+ 0) (cong (bool 1 0 ∘ bool true true) (sym (it-doesn't (y ≟ x) (x≢y ∘ sym))))

    lemma₂ : ∀ x xs → x # x ∷ xs ≡ 0
    lemma₂ x xs with x ≟ x
    ... | no x≢x = absurd (x≢x refl)
    ... | yes _ = refl

  size-alg : Ψ[ xs ⦂ 𝒦 A ] ↦ ℕ
  size-alg .fst ∅ = zero
  size-alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = (x # xs) + P⟨xs⟩
  size-alg .snd .c-trunc _ = Discrete→isSet discreteℕ
  size-alg .snd .c-com x y xs P⟨xs⟩ = sym (+-assoc (x # y ∷ xs) (y # xs) P⟨xs⟩) ; cong (_+ P⟨xs⟩) (lemma₁ x y xs) ; +-assoc (y # x ∷ xs) (x # xs) P⟨xs⟩ 
  size-alg .snd .c-dup x xs P⟨xs⟩ = cong (_+ ((x # xs) + P⟨xs⟩)) (lemma₂ x xs)

_-_ : 𝒦 A → 𝒦 A → 𝒦 A
xs - ys = ⟦ alg xs ⟧ ys
  where
  alg : ∀ xs → Ψ[ ys ⦂ 𝒦 A ] ↦ 𝒦 A
  alg xs .fst ∅ = xs
  alg _  .fst (y ∷ _ ⟨ xs-ys ⟩) = xs-ys \\ y
  alg xs .snd .c-trunc _ = trunc
  alg xs .snd .c-com x y _ P⟨xs⟩ = \\-com y x P⟨xs⟩
  alg xs .snd .c-dup x _ ys = \\-idem x ys

open import Data.Nat.Properties
open import HITs.PropositionalTruncation

∷-size : ∀ x xs → size xs ≤′ size (x ∷ xs)
∷-size x xs with x ∈? xs
... | yes x∈xs = zero , refl
... | no  x∉xs = 1 , refl

\\-size : ∀ x xs → size (xs \\ x) ≤′ size xs
\\-size x = ⟦ alg x ⟧
  where
  alg : ∀ x → Ψ[ xs ⦂ 𝒦 A ] ↦ size (xs \\ x) ≤′ size xs
  alg x .snd = prop-coh λ _ → isProp-≤′ _ _
  alg x .fst ∅ = zero , refl
  alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) with x ≟ y | y ∈? xs
  ... | yes x≡y | yes y∈xs = P⟨xs⟩
  ... | no  x≢y | yes y∈xs = subst (_≤′ size xs) (cong (_+ size (xs \\ x)) (sym (cong (bool 1 0) (it-does (y ∈? (xs \\ x)) (≢-rem y x (x≢y ∘ sym) xs y∈xs))))) P⟨xs⟩
  ... | yes x≡y | no  y∉xs = ≤′-trans (size (xs \\ x)) _ _ P⟨xs⟩ (1 , refl)
  ... | no  x≢y | no  y∉xs = subst (_≤′ 1 + size xs) (sym (cong (_+ size (xs \\ x)) (cong (bool 1 0) (it-doesn't (y ∈? (xs \\ x)) (y∉xs ∘ rem-∈ y x xs))))) (p≤′p _ _ P⟨xs⟩ )

\\-∈-size : ∀ x xs → x ∈ xs → size (xs \\ x) <′ size xs
\\-∈-size x = ⟦ alg x ⟧
  where
  alg : ∀ x → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ xs → size (xs \\ x) <′ size xs)
  alg x .snd = prop-coh λ xs → isProp→ (isProp-<′ _ _)
  alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) x∈xs with x ≟ y | y ∈? xs
  ... | yes x≡y | no  y∉xs = ≤⇒s< _ _ (\\-size x xs)
  ... | yes x≡y | yes y∈xs = P⟨xs⟩ (subst (_∈ xs) (sym x≡y) y∈xs)
  ... | no  x≢y | yes y∈xs = subst (_<′ size xs) (sym (cong (_+ size (xs \\ x)) (cong (bool 1 0) (it-does (y ∈? (xs \\ x)) ((≢-rem y x (x≢y ∘ sym) xs y∈xs)))))) (P⟨xs⟩ (∥rec∥ (isProp-∈ x xs) (absurd ∘ ∥rec∥ isProp⊥ x≢y ▿ id) x∈xs))
  ... | no  x≢y | no  y∉xs = subst (_<′ suc (size xs)) (sym (cong (_+ size (xs \\ x)) (cong (bool 1 0) (it-doesn't (y ∈? (xs \\ x)) (y∉xs ∘ rem-∈ y x xs)))) ) (p<′p _ _ (P⟨xs⟩ ((∥rec∥ (isProp-∈ x xs) (absurd ∘ ∥rec∥ isProp⊥ x≢y ▿ id) x∈xs))))

-‿∈ : ∀ x xs ys → x ∈ xs → x ∉ ys → x ∈ xs - ys
-‿∈ x xs = ⟦ alg x xs ⟧
  where
  alg : ∀ x xs → Ψ[ ys ⦂ 𝒦 A ] ↦ (x ∈ xs → x ∉ ys → x ∈ xs - ys)
  alg x xs .snd = prop-coh (λ ys → isProp→ (isProp→ (isProp-∈ x (xs - ys))))
  alg x xs .fst ∅ x∈xs x∉ys = x∈xs
  alg x xs .fst (y ∷ ys ⟨ P⟨ys⟩ ⟩) x∈xs x∉ys =
    ≢-rem x y (x∉ys ∘ ∣_∣ ∘ inl ∘ ∣_∣) (xs - ys) (P⟨ys⟩ x∈xs (x∉ys ∘ ∣_∣ ∘ inr))

open import WellFounded

module _ (Dom : 𝒦 A) where
\end{code}
%<*noeth-acc>
\begin{code}
  data NoethAcc (seen : 𝒦 A) : Type a where
    nacc : (∀ x → x ∈ Dom → x ∉ seen → NoethAcc (x ∷ seen)) → NoethAcc seen
\end{code}
%</noeth-acc>
\begin{code}

  infix 4 _≺′_
  _≺′_ : 𝒦 A → 𝒦 A → Type
  xs ≺′ ys = size xs <′ size ys

  noeth′ : ∀ seen → Acc _≺′_ (Dom - seen) → NoethAcc seen
  noeth′ seen (acc wf) =
    nacc λ x x∈d x∉s →
      noeth′
        (x ∷ seen)
        (wf (Dom - (x ∷ seen)) (\\-∈-size x (Dom - seen) (-‿∈ x Dom seen x∈d x∉s)))

  opaque
    noeth : NoethAcc ∅
    noeth = noeth′ ∅ (fun-wellFounded size <-wellFounded Dom)
\end{code}
