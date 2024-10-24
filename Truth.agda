{-# OPTIONS --safe #-}

module Truth where

open import Prelude
  hiding (⊤; tt)
  renaming (Poly-⊤ to ⊤; Poly-tt to tt)



infix 3 _∥_
record Ω p : Type (ℓsuc p) where
  constructor _∥_; no-eta-equality
  field  ProofOf  : Type p
         IsProp   : isProp ProofOf
open Ω public
True : Ω a
ProofOf  True = ⊤
IsProp   True _ _ = refl

open import Cubical.Foundations.HLevels using (isPropIsOfHLevel)

cong-∥ : (x y : Ω a) → (lhs : ProofOf x ≡ ProofOf y) → PathP (λ i → isProp (lhs i)) (IsProp x) (IsProp y) → x ≡ y
cong-∥ x y lhs rhs i .ProofOf = lhs i
cong-∥ x y lhs rhs i .IsProp = rhs i

Ω≡ : (x y : Ω a) → ProofOf x ≡ ProofOf y → x ≡ y
Ω≡ x y p = 
  cong-∥ x y p
    (J (λ y idxy → ∀ lhs rhs → PathP (λ i → isProp (idxy i)) lhs rhs) (isPropIsOfHLevel 1) p (IsProp x) (IsProp y))

private
  variable X Y Z : Ω a

_iff_ : (ProofOf X → ProofOf Y) → (ProofOf Y → ProofOf X) → X ≡ Y
_iff_ {X = x} {Y = y} lhs rhs =
  Ω≡ x y (isoToPath (iso lhs rhs (λ _ → y .IsProp _ _) λ _ → x .IsProp _ _))



proves-lhs : (x : Ω a) → ProofOf x → ProofOf x ≡ ⊤
proves-lhs x p = isoToPath (iso (const tt) (const p) (λ _ → refl) λ _ → IsProp x _ _)


proves : ProofOf X → X ≡ True
proves p = const tt iff const p

module _ {a : Level} where
  False : Ω a
  False .ProofOf = Poly-⊥ 
  False .IsProp ()

  disproves :  (ProofOf X → ⊥)
          →   X ≡ False
  disproves p = (absurd ∘ p) iff λ ()

extract : {x : Ω a} → x ≡ True → ProofOf x
extract p = subst ProofOf (sym p) tt

open import Cubical.Foundations.HLevels

Truth⇔hProp : Ω a ⇔ hProp a
Truth⇔hProp .fun x .fst = x .ProofOf
Truth⇔hProp .fun x .snd = x .IsProp
Truth⇔hProp .inv x .ProofOf = x .fst
Truth⇔hProp .inv x .IsProp = x .snd
Truth⇔hProp .rightInv b = refl
Truth⇔hProp .leftInv x i .ProofOf = x .ProofOf
Truth⇔hProp .leftInv x i .IsProp = x .IsProp

abstract
  isSetΩ : isSet (Ω a)
  isSetΩ = subst isSet (sym (isoToPath Truth⇔hProp)) isSetHProp

open import Cubical.HITs.PropositionalTruncation

interleaved mutual
  infixl 7 _|∧|_
  _|∧|_ : Ω a → Ω a → Ω _
  infixl 6 _|∨|_
  _|∨|_ : Ω a → Ω b → Ω _
  infixr 5 _|→|_
  _|→|_ : Ω a → Ω b → Ω _

  ProofOf (X |∧| Y) = ProofOf X × ProofOf Y
  ProofOf (X |→| Y) = ProofOf X → ProofOf Y
  ProofOf (X |∨| Y) = ∥ ProofOf X ⊎ ProofOf Y ∥
  IsProp (_  |→| Y) = isProp→ (IsProp Y)
  IsProp (x |∧| y) = isProp× (x .IsProp) (y .IsProp)
  IsProp (x |∨| y) = squash

|∀| : (A → Ω b) → Ω _
ProofOf (|∀| f) = ∀ x → ProofOf (f x)
IsProp   (|∀| f) = isPropΠ λ x → IsProp (f x)

_|↔|_ : Ω a → Ω b → Ω _
X |↔| Y = (X |→| Y) |∧| (Y |→| X)

|→|-id : (x : Ω a) → x |→| x ≡ True
|→|-id x = proves id

Not : Ω a → Ω a
Not x .ProofOf = ¬ x .ProofOf
Not x .IsProp = isProp→ λ ()

|→|-idˡ : (x : Ω a) → True |→| x ≡ x
|→|-idˡ {a = a} x = (_$ (tt {ℓ = a})) iff const

|→|-annʳ : (x : Ω a) → x |→| True {a = b} ≡ True
|→|-annʳ x = const tt iff (λ _ _ → tt)

|→|-annˡ : (x : Ω a) → False {a = b} |→| x ≡ True
|→|-annˡ x = (λ _ → tt) iff λ _ ()

Ω∣_∣ : Type a → Ω a
ProofOf  Ω∣ P ∣ = ∥ P ∥
IsProp   Ω∣ P ∣ = squash

infix 5.5 _|≡|_
_|≡|_ : A → A → Ω _
x |≡| y = Ω∣ x ≡ y ∣

|T| : Bool → Ω ℓzero
|T| b .ProofOf = T b
|T| b .IsProp = isPropT b

|→|-trans : (x y z : Ω a) → ((x |→| y) |∧| (y |→| z)) |→| (x |→| z) ≡ True
|→|-trans x y z = const tt iff const (uncurry (flip _∘_))

|→|-curry : (X Y Z : Ω a) → (X |∧| Y |→| Z) ≡ (X |→| Y |→| Z)
|→|-curry _ _ _ = curry iff uncurry

|→|-|∧| : (x y z : Ω a) → (x |→| (y |∧| z)) ≡ (x |→| y) |∧| (x |→| z)
|→|-|∧| _ _ _ = (λ f → fst ∘ f , snd ∘ f) iff λ { (f , g) x → f x , g x }

|∨|-|→| : (x y z : Ω a) → ((x |∨| y) |→| z) ≡ (x |→| z) |∧| (y |→| z)
|∨|-|→| _ _ z =
    (λ f → f ∘ ∣_∣ ∘ inl , f ∘ ∣_∣ ∘ inr) iff
    λ { (f , g) → rec (z .IsProp) (either f g) }

∧-com : (x y : Ω a) → x |∧| y ≡ y |∧| x
∧-com _ _ = (λ { (x , y) → (y , x) }) iff λ { (x , y) → y , x }

∧-idem : (x : Ω a) → x |∧| x ≡ x
∧-idem _ = fst iff (λ x → x , x)

∨-idem : (x : Ω a) → x |∨| x ≡ x
∨-idem x = (rec (x .IsProp) (either id id)) iff (∣_∣ ∘ inl)

∨-com : (x y : Ω a) → x |∨| y ≡ y |∨| x
∨-com x y = (rec squash (∣_∣ ∘ either inr inl)) iff (rec squash (∣_∣ ∘ either inr inl))

∧-ann : (x : Ω a) → x |∧| (False {a}) ≡ False
∧-ann x = snd iff λ ()

refute : (x : Ω a) → ¬ ProofOf x → x ≡ False
refute x ¬p = (absurd ∘ ¬p) iff λ ()

∨-assoc : (x y z : Ω a) → (x |∨| y) |∨| z ≡ x |∨| (y |∨| z)
∨-assoc x y z =
    (rec squash (either (rec squash  (∣_∣ ∘ mapʳ (∣_∣ ∘ inl))) (∣_∣ ∘ inr ∘ ∣_∣ ∘ inr ))) iff
    (rec squash (either (∣_∣ ∘ inl ∘ ∣_∣ ∘ inl) (rec squash (∣_∣ ∘ mapˡ (∣_∣ ∘ inr) ))))

∧-assoc : (x y z : Ω a) → (x |∧| y) |∧| z ≡ x |∧| (y |∧| z)
∧-assoc x y z =
    (λ { ((x , y) , z) → x , y , z }) iff
    λ { (x , y , z) → (x , y)  , z }

∧-id : (x : Ω a) → (True {a}) |∧| x ≡ x
∧-id x = snd iff (tt ,_)

∨-ann : (x : Ω a) → x |∨| (True {a}) ≡ True
∨-ann x = (const tt) iff (∣_∣ ∘ inr)

∨-id : (x : Ω a) → x |∨| (False {a}) ≡ x
∨-id x = (rec (x .IsProp) (either id (λ ()))) iff (∣_∣ ∘ inl)

∨-idˡ : (x : Ω a) → (False {a}) |∨| x ≡ x
∨-idˡ x = (rec (x .IsProp) (either (λ ()) id)) iff (∣_∣ ∘ inr)

∧-distrib-∨ : (x y z : Ω a) → x |∧| (y |∨| z) ≡ (x |∧| y) |∨| (x |∧| z)
∧-distrib-∨ x y z =
    (uncurry (λ xp → rec squash (∣_∣ ∘ map-⊎ (xp ,_) (xp ,_)) )) iff
    (rec (isProp× (x .IsProp) squash) (either (map₂ (∣_∣ ∘ inl)) (map₂ (∣_∣ ∘ inr))))


∨-distrib-∧ : (x y z : Ω a) → x |∨| (y |∧| z) ≡ (x |∨| y) |∧| (x |∨| z)
∨-distrib-∧ x y z =
    (rec (isProp× squash squash) (either (λ x → ∣ inl x ∣ , ∣ inl x ∣) λ { (yp , zp) → ∣ inr yp ∣ , ∣ inr zp ∣ })) iff
    (uncurry (rec2 squash  λ { (inl x) _ → ∣ inl x ∣ ; _ (inl x) → ∣ inl x ∣ ; (inr y) (inr z) → ∣ inr (y , z) ∣  }))
