{-# OPTIONS --safe #-}

module HITs.SetQuotients where

open import Cubical.HITs.SetQuotients
  using (eq/; squash/; [_]; _/_)
  renaming (rec to rec/; elimProp to elimProp/; elim to elim/; effective to effective/)
  public

open import Level
open import Cubical.Foundations.Everything using (isSet; isSetΠ; isProp; isPropΠ; isPropΠ2)
open import Path

import Cubical.Relation.Binary.Base
open Cubical.Relation.Binary.Base.BinaryRelation using (isPropValued; isEquivRel) public

private variable R S T : A → A → Type b

rec2/ : isSet C
  → (f : A → B → C)
  → (∀ a b c → R a b → f a c ≡ f b c)
  → (∀ a b c → S b c → f a b ≡ f a c)
  → A / R → B / S → C
rec2/ set f feql feqr =
  rec/ (isSetΠ (λ _ → set))
    (λ a → rec/ set (f a) (feqr a))
    (λ a b r → funExt (elimProp/ (λ _ → set _ _) (λ c → feql a b c r)))

elimProp2/ : {P : A / R → B / S → Type c}
  → (∀ x y → isProp (P x y))
  → (∀ a b → P [ a ] [ b ])
  → ∀ x y → P x y
elimProp2/ prop f =
  elimProp/ (λ x → isPropΠ (prop x)) λ a →
  elimProp/ (prop [ a ]) (f a)

elimProp3/ : ∀ {ℓ} {P : A / R → B / S → C / T → Type ℓ}
  → (∀ x y z → isProp (P x y z))
  → (∀ a b c → P [ a ] [ b ] [ c ])
  → ∀ x y z → P x y z
elimProp3/ prop f =
  elimProp/ (λ x → isPropΠ2 (prop x)) λ a →
  elimProp2/ (prop [ a ]) (f a)

open import Function
open import HITs.PropositionalTruncation
open import HLevels

module _ {A : Type a} {_~_ : A → A → Type b} where
  []-surj : Surjective ([_] {A = A} {R = _~_})
  []-surj =
      elim/
        (λ _ → isProp→isSet squash)
        (λ x → ∣ x ,↠ refl ∣ )
        λ x y r →
          J (λ z p → ∀ pr → PathP (λ i → ∥ Surjected [_] (p i) ∥) ∣ x ,↠ refl ∣ ∣ y ,↠ pr ∣)
            (λ _ → squash _ _)
            (eq/ _ _ r)
            refl

open import Data.Unit
open import Isomorphism

/⊤⇔∥∥ : A / (λ _ _ → ⊤) ⇔ ∥ A ∥
/⊤⇔∥∥ .fun = rec/ (isProp→isSet squash) ∣_∣ λ _ _ _ → squash _ _
/⊤⇔∥∥ .inv = ∥rec∥ (elimProp2/ squash/ λ x y → eq/ x y tt) [_]
/⊤⇔∥∥ .rightInv x = squash _ _
/⊤⇔∥∥ .leftInv  = elimProp/ (λ _ → squash/ _ _) λ _ → refl

