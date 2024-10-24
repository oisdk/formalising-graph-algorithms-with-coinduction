{-# OPTIONS --safe #-}

open import Prelude

module Codata.Chain {ℓ} (S : Type ℓ)  where

open import Data.Link S

record Chain (A : Type a) : Type (ℓ ℓ⊔ a) where
  coinductive; constructor _◂_
  field  head  : A
         tail  : Link (Chain A)
open Chain

module _ (ψ : A → B × Link A) where
  ana     : A → Chain B
  ana′    : B × Link A → Chain B
  map-ana : Link A → Link (Chain B)

  ana = ana′ ∘ ψ

  ana′ r .head = r .fst
  ana′ r .tail = map-ana (r .snd)

  map-ana (w ∝ x) = w ∝ ana x
  map-ana ⟨⟩ = ⟨⟩

cout : Chain A → A × Link (Chain A)
cout = head ▵ tail

map-chain : (A → B) → Chain A → Chain B
map-chain f = ana (map₁ f ∘ cout)

module _ (f : A → B) (ψ : C → A × Link C) where
  map∘ana : ∀ r → map-chain f (ana ψ r) ≡ ana (map₁ f ∘ ψ) r
  map∘ana′ : ∀ r → map-ana (map₁ f ∘ cout) (map-ana ψ r) ≡ map-ana (map₁ f ∘ ψ) r

  map∘ana r i .head = f (ψ r .fst)
  map∘ana r i .tail = map∘ana′ (ψ r .snd) i

  map∘ana′ (s ∝ x) = cong (s ∝_) (map∘ana x)
  map∘ana′ ⟨⟩ = refl

module _ (R : A → A → Type c)  where
  R″ : Link A → Link A → Type (ℓ ℓ⊔ c)
  R″ ⟨⟩ ⟨⟩ = Poly-⊤
  R″ (x ∝ xs) (y ∝ ys) = (x ≡ y) × R xs ys
  R″ _ _ = Poly-⊥

  R′ : B × Link A → B × Link A → Type _
  R′ (x , xs) (y , ys) = x ≡ y × R″ xs ys

  module _ (ψ : A → B × Link A) (p : ∀ x y → R x y → R′ (ψ x) (ψ y)) where
    ana-bisim : ∀ x y → R x y → ana ψ x ≡ ana ψ y
    ana-bisim′ : ∀ x y → R″ x y → map-ana ψ x ≡ map-ana ψ y

    ana-bisim x y r i .head = p x y r .fst i
    ana-bisim x y r i .tail = ana-bisim′ (ψ x .snd) (ψ y .snd) (p x y r .snd) i

    ana-bisim′ (x ∝ xs) (y ∝ ys) (r , rs) = cong₂ _∝_ r (ana-bisim xs ys rs)
    ana-bisim′ ⟨⟩ ⟨⟩ r = refl

Chain⁺ : Type a → Type (ℓ ℓ⊔ a)
Chain⁺ A = Link (Chain A)

tabulate  : (ℕ → Link A) → Chain⁺ A
tabulate⁺ : (ℕ → Link A) → Link A → Chain⁺ A
tabulate′ : (ℕ → Link A) → A → Chain A

tabulate  f = tabulate⁺ f (f zero)

tabulate⁺ f (s ∝ x) = s ∝ tabulate′ f x
tabulate⁺ f ⟨⟩ = ⟨⟩

tabulate′ f x .head = x
tabulate′ f x .tail = tabulate (f ∘ suc)

open import Data.Nat.Order

module _ {A : Type a} where
  _≲_ : Maybe A → Maybe A → Type _
  just x  ≲ y = ⊤
  nothing ≲ just _ = ⊥
  nothing ≲ nothing = ⊤

  isProp-≲ : ∀ {x y} → isProp (x ≲ y)
  isProp-≲ {fsuc x} {y} _ _ = refl
  isProp-≲ {⟨⟩} {fsuc x} ()
  isProp-≲ {⟨⟩} {⟨⟩} _ _ = refl

module _ {A : Type a} where

  index : Chain⁺ A → ℕ → Link A
  index′ : S → Chain A → ℕ → Link A

  index′ s xs zero    = s ∝ head xs
  index′ s xs (suc n) = index (tail xs) n

  index ⟨⟩ _ = nothing
  index (s ∝ xs) = index′ s xs

  final : (ℕ → Link A) → Type _
  final p = ∀ m n → m ≤ n → p m ≲ p n

  final-ind : ∀ xs → final (index xs)
  final-ind ⟨⟩ m n m≤n = tt
  final-ind (s ∝ x) zero zero m≤n = tt
  final-ind (s ∝ x) zero (suc n) m≤n = tt
  final-ind (s ∝ x) (suc m) (suc n) m≤n = final-ind (tail x) m n m≤n

  isProp-final : ∀ f → isProp (final f)
  isProp-final f = isPropΠ λ m → isPropΠ λ n → isProp→ isProp-≲

  index∘tabulate : ∀ f → final f → ∀ n → index (tabulate f) n ≡ f n
  index∘tabulate f p zero with f zero
  index∘tabulate f p zero | _ ∝ _ = refl
  index∘tabulate f p zero | ⟨⟩ = refl
  index∘tabulate f p (suc n) with f zero | f (suc n) | inspect f (suc n) | p zero (suc n) tt
  ... | s ∝ x | _ | 〖 fs 〗 | q = index∘tabulate (f ∘ suc) (λ m n → p (suc m) (suc n)) n ; fs
  ... | ⟨⟩     | ⟨⟩ | _ | q = refl

  tabulate∘index : ∀ x → tabulate (index x) ≡ x
  tabulate∘index′ : ∀ s x → tabulate′ (index′ s x) (head x) ≡ x

  tabulate∘index ⟨⟩ i = ⟨⟩
  tabulate∘index (s ∝ x) i = s ∝ tabulate∘index′ s x i

  tabulate∘index′ s x i .head = head x
  tabulate∘index′ s x i .tail = tabulate∘index (tail x) i

Chain⁺′ : Type a → Type _
Chain⁺′ A = Σ (ℕ → Link A) final

open import Cubical.Data.Sigma using (Σ≡Prop)

chain⁺-iso : Chain⁺ A ⇔ Chain⁺′ A
chain⁺-iso .fun xs .fst = index xs
chain⁺-iso .fun xs .snd = final-ind xs
chain⁺-iso .inv (xs , _) = tabulate xs
chain⁺-iso .rightInv (f , p) = Σ≡Prop isProp-final (funExt (index∘tabulate f p))
chain⁺-iso .leftInv = tabulate∘index

chain-iso : Chain A ⇔ (A × Chain⁺ A)
chain-iso .fun xs = xs .head , xs .tail
chain-iso .inv (x , xs) = x ◂ xs
chain-iso .rightInv _ = refl
chain-iso .leftInv x i .head = x .head
chain-iso .leftInv x i .tail = x .tail

open import Data.Maybe.Properties

module _ (isSetS : isSet S) (isSetA : isSet A) where
  isSetChain⁺′ : isSet (Chain⁺′ A)
  isSetChain⁺′ = isSetΣ (isSetΠ (λ _ → isOfHLevelMaybe 0 (isSet× isSetS isSetA))) λ f → isProp→isSet (isProp-final f)

  isSetChain : isSet (Chain A)
  isSetChain =
    subst
      isSet
      (isoToPath (sym-⇔ chain-iso))
      (isSet× isSetA (subst isSet (isoToPath (sym-⇔ chain⁺-iso)) isSetChain⁺′))
