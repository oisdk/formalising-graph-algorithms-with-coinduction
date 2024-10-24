{-# OPTIONS --safe #-}

module Decidable where

open import Level
open import Data.Bool
open import Path
open import Data.Unit
open import Data.Empty
open import Data.Sigma

Reflects : Type a → Bool → Type a
Reflects A = bool′ (¬ A) A

record Dec {a} (A : Type a) : Type a where
  constructor _because_
  field
    does  : Bool
    why   : Reflects A does
open Dec public

pattern yes p  = true   because p
pattern no ¬p  = false  because ¬p

map-reflects : (A → B) → (¬ A → ¬ B) → ∀ {d} → Reflects A d → Reflects B d
map-reflects {A = A} {B = B} to fro {d = d} = bool {P = λ d → Reflects A d → Reflects B d} fro to d

Reflects-T : ∀ b → Reflects (T b) b
Reflects-T = bool (λ z → z) _

map-dec : (A → B) → (¬ A → ¬ B) → Dec A → Dec B
map-dec to fro dec .does = dec .does
map-dec to fro dec .why = map-reflects to fro (dec .why)

iff-dec : (A → B) → (B → A) → Dec A → Dec B
iff-dec to fro = map-dec to (λ ¬A B → ¬A (fro B))

infixr 1 dec
dec : (A → B) → (¬ A → B) → Dec A → B
dec {A = A} {B = B} on-yes on-no d = bool {P = λ d → Reflects A d → B} on-no on-yes (d .does) (d .why)

syntax dec (λ yv → ye) (λ nv → ne) dc = ∣ dc ∣yes yv ⇒ ye ∣no nv ⇒ ne

open import Data.Maybe

does? : Dec A → Maybe A
does? = dec just (λ _ → nothing)

T? : (b : Bool) → Dec (T b)
T? b .does = b
T? false .why ()
T? true  .why = _

dec-bool : (b : Bool) → (T b → A) → (A → T b) → Dec A
dec-bool b to fro .does = b
dec-bool false to fro .why = fro
dec-bool true  to fro .why = to _

open import Path

it-does : (d : Dec A) → A → does d ≡ true
it-does (yes _) _ = refl
it-does (no ¬A) A = absurd (¬A A)

it-doesn't : (d : Dec A) → ¬ A → does d ≡ false
it-doesn't (no _)  _  = refl
it-doesn't (yes A) ¬A = absurd (¬A A)

both-do : (x : Dec A) (y : Dec B) → ((A → B) × (B → A)) → does x ≡ does y
both-do x (no ¬B) A↔B = it-doesn't x λ A → ¬B (A↔B .fst A)
both-do x (yes B) A↔B = it-does x (A↔B .snd B)

from-does : (x : Dec A) → T (does x) → A
from-does (yes x) p = x

from-doesn't : (x : Dec A) → T (neg (does x)) → ¬ A
from-doesn't (no x) p = x

Stable : Type a → Type a
Stable A = ¬ ¬ A → A

open import HLevels
open import Data.Empty.Properties
open import Cubical.Foundations.Everything
  using (hcomp; _∧_; i0; i1)

Stable≡→isSet : ∀ {ℓ} {A : Type ℓ} → (st : ∀ (a b : A) → Stable (a ≡ b)) → isSet A
Stable≡→isSet {A = A} st a b p q j i =
  let f : (x : A) → a ≡ x → a ≡ x
      f x p = st a x (λ h → h p)
      fIsConst : (x : A) → (p q : a ≡ x) → f x p ≡ f x q
      fIsConst = λ x p q i → st a x (isProp¬ (λ h → h p) (λ h → h q) i)
      rem : (p : a ≡ b) → PathP (λ i → a ≡ p i) (f a refl) (f b p)
      rem p j = f (p j) (λ i → p (i ∧ j))
  in hcomp (λ k → λ { (i = i0) → f a refl k
                    ; (i = i1) → fIsConst b p q j k
                    ; (j = i0) → rem p i k
                    ; (j = i1) → rem q i k }) a

Dec→Stable : (A : Type a) → Dec A → Stable A
Dec→Stable A (yes x) = λ _ → x
Dec→Stable A (no x) = λ f → absurd (f x)

isPropDec : (Aprop : isProp A) → isProp (Dec A)
isPropDec Aprop (yes a) (yes a') i = yes (Aprop a a' i)
isPropDec Aprop (yes a) (no ¬a) = absurd (¬a a)
isPropDec Aprop (no ¬a) (yes a) = absurd (¬a a)
isPropDec {A = A} Aprop (no ¬a) (no ¬a') i = no (isProp¬ ¬a ¬a' i)

not : Dec A → Dec (¬ A)
not x .does = neg (does x)
not (no  ¬A) .why = ¬A
not (yes  A) .why ¬A = ¬A A

_and_ : Dec A → Dec B → Dec (A × B)
(x and y) .does = does x && does y
(no ¬A and _) .why (A , _) = ¬A A
(yes A and no ¬B) .why (_ , B) = ¬B B
(yes A and yes B) .why = A , B

open import Data.Sum.Definition

_or_ : Dec A → Dec B → Dec (A ⊎ B)
(x or y) .does = does x || does y
(yes A or y) .why = inl A
(no ¬A or yes B) .why = inr B
(no ¬A or no ¬B) .why (inl A) = ¬A A
(no ¬A or no ¬B) .why (inr B) = ¬B B

open import HITs.PropositionalTruncation

∥refute∥ : Dec A → ∥ A ∥ → A
∥refute∥ (no ¬A) ∣A∣ = absurd (∥rec∥ isProp⊥ ¬A ∣A∣)
∥refute∥ (yes A) _   = A
