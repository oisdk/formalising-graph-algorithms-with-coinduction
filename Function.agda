{-# OPTIONS --safe #-}

module Function where

open import Level

infixr 9 _∘′_
_∘′_ : ∀ {A : Type a} {B : A → Type b} {C : {x : A} → B x → Type c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘′ g = λ x → f (g x)
{-# INLINE _∘′_ #-}

infixr 9 _∘_
_∘_ : (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)
{-# INLINE _∘_ #-}

flip : ∀ {A : Type a} {B : Type b} {C : A → B → Type c} →
        ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y
{-# INLINE flip #-}

id : ∀ {A : Type a} → A → A
id x = x
{-# INLINE id #-}

const : A → B → A
const x _ = x
{-# INLINE const #-}

infixr -1 _$_
_$_ : ∀ {A : Type a} {B : A → Type b}
      → (∀ (x : A) → B x)
      → (x : A)
      → B x
f $ x = f x
{-# INLINE _$_ #-}

infixl 0 _|>_
_|>_ : ∀ {A : Type a} {B : A → Type b}
      → (x : A)
      → (∀ (x : A) → B x)
      → B x
_|>_ = flip _$_
{-# INLINE _|>_ #-}

infixl 1 _⟨_⟩_
_⟨_⟩_ : A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y
{-# INLINE _⟨_⟩_ #-}

infixl 0 the
the : (A : Type a) → A → A
the _ x = x
{-# INLINE the #-}

-- A way to write type annotations inline
syntax the A x = x ⦂ A

-- You can write
--   x = true ⦂ Bool
-- or
--   x = true ⦂ Bool ⦂ Bool
-- etc

-- It's useful to sometimes have a functor arrow that doesn't
-- have -∞ precedence
infixr 0.5 _→′_
_→′_ : Type a → Type b → Type (a ℓ⊔ b)
A →′ B = A → B

infix 0 case_of_
case_of_ : A → (A → B) → B
case x of f = f x
{-# INLINE case_of_ #-}

infixr -1 _⇒_
_⇒_ : (A → Type b) → (A → Type c) → Type _
F ⇒ G = ∀ {x} → F x → G x

infixr -1 _↣_ _↠_ _↠!_

open import Path

Injective : (f : A → B) → Type _
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

open import Data.Sigma

_↣_ : Type a → Type b → Type _
A ↣ B = Σ[ f ⦂ (A → B) ] × Injective f

↣-refl : A ↣ A
↣-refl .fst = id
↣-refl .snd = id

↣-trans : A ↣ B → B ↣ C → A ↣ C
↣-trans (f , fi) (g , gi) .fst = g ∘ f
↣-trans (f , fi) (g , gi) .snd = fi ∘ gi

record Surjected {A : Type a} {B : Type b} (f : A → B) (y : B) : Type (a ℓ⊔ b) where
  no-eta-equality; constructor _,↠_
  field
    image    : A
    reflects : f image ≡ y
open Surjected public

open import Isomorphism

Surjected⇔Σ : (f : A → B) (y : B) → Surjected f y ⇔ (∃ x × f x ≡ y)
Surjected⇔Σ f y .fun s = image s , reflects s
Surjected⇔Σ f y .inv s .image = fst s
Surjected⇔Σ f y .inv s .reflects = snd s
Surjected⇔Σ f y .rightInv s = refl
Surjected⇔Σ f y .leftInv s i .image = image s
Surjected⇔Σ f y .leftInv s i .reflects = reflects s

open import HLevels
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

Surj≡Prop : (f : A → B) (y : B) → isSet B → {lhs rhs : Surjected f y} → (image lhs ≡ image rhs) → lhs ≡ rhs
Surj≡Prop f y s {lhs = lhs} {rhs = rhs} p =
  sym (Surjected⇔Σ f y .leftInv _) ;
  cong (Surjected⇔Σ f y .inv) (Σ≡Prop (λ _ → s _ _) p) ;
  Surjected⇔Σ f y .leftInv _

SplitSurjective : (f : A → B) → Type _
SplitSurjective f =  ∀ y → Surjected f y

_↠!_ : Type a → Type b → Type _
A ↠! B = Σ[ f ⦂ (A → B) ] × SplitSurjective f

open import HITs.PropositionalTruncation

Surjective : (f : A → B) → Type _
Surjective f = ∀ y → ∥ Surjected f y ∥

_↠_ : Type a → Type b → Type _
A ↠ B = Σ[ f ⦂ (A → B) ] × Surjective f
