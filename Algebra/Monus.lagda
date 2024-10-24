\begin{code}
{-# OPTIONS --safe #-}

-- This is a file for dealing with Monuses: these are monoids that are like the
-- positive half of a group. Much of my info on them comes from these papers:
--
-- * Wehrung, Friedrich. ‘Injective Positively Ordered Monoids I’. Journal of
--   Pure and Applied Algebra 83, no. 1 (11 November 1992): 43–82.
--   https://doi.org/10.1016/0022-4049(92)90104-N.
-- * Wehrung, Friedrich. ‘Embedding Simple Commutative Monoids into Simple
--   Refinement Monoids’. Semigroup Forum 56, no. 1 (January 1998): 104–29.
--   https://doi.org/10.1007/s00233-002-7008-0.
-- * Amer, K. ‘Equationally Complete Classes of Commutative Monoids with Monus’.
--   Algebra Universalis 18, no. 1 (1 February 1984): 129–31.
--   https://doi.org/10.1007/BF01182254.
-- * Wehrung, Friedrich. ‘Metric Properties of Positively Ordered Monoids’.
--   Forum Mathematicum 5, no. 5 (1993).
--   https://doi.org/10.1515/form.1993.5.183.
-- * Wehrung, Friedrich. ‘Restricted Injectivity, Transfer Property and
--   Decompositions of Separative Positively Ordered Monoids.’ Communications in
--   Algebra 22, no. 5 (1 January 1994): 1747–81.
--   https://doi.org/10.1080/00927879408824934.
--
-- These monoids have a preorder defined on them, the algebraic preorder:
-- 
--   x ≤ y = ∃ z × (y ≡ x ∙ z)
--
-- The _∸_ operator extracts the z from above, if it exists.

module Algebra.Monus where

open import Prelude hiding ([_])
open import Algebra
open import Relation.Binary
open import Path.Reasoning
open import Function.Reasoning

module _ {ℓ₁} (𝑆 : Type ℓ₁) where
-- Positively ordered monoids.
--
-- These are monoids which have a preorder that respects the monoid operation
-- in a straightforward way.
  record POM ℓ₂ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
    field commutativeMonoid : CommutativeMonoid 𝑆
    open CommutativeMonoid commutativeMonoid public
    field preorder : Preorder 𝑆 ℓ₂
    open Preorder preorder public renaming (refl to ≤-refl)
    field
      positive : ∀ x → ε ≤ x
      ≤-cong : ∀ x {y z} → y ≤ z → x ∙ y ≤ x ∙ z

    x≤x∙y : ∀ {x y} → x ≤ x ∙ y
    x≤x∙y {x} {y} = subst (_≤ x ∙ y) (∙ε x) (≤-cong x (positive y))

    ≤-congʳ : ∀ x {y z} → y ≤ z → y ∙ x ≤ z ∙ x
    ≤-congʳ x {y} {z} p = subst₂ _≤_ (comm x y) (comm x z) (≤-cong x p)

    alg-≤-trans : ∀ {x y z k₁ k₂} → y ≡ x ∙ k₁ → z ≡ y ∙ k₂ → z ≡ x ∙ (k₁ ∙ k₂)
    alg-≤-trans {x} {y} {z} {k₁} {k₂} y≡x∙k₁ z≡y∙k₂ =
      z             ≡⟨ z≡y∙k₂ ⟩
      y ∙ k₂        ≡⟨ cong (_∙ k₂) y≡x∙k₁ ⟩
      (x ∙ k₁) ∙ k₂ ≡⟨ assoc x k₁ k₂ ⟩
      x ∙ (k₁ ∙ k₂) ∎

    infix 4 [_]_≺_
    [_]_≺_ : 𝑆 → 𝑆 → 𝑆 → Type _
    [ s ] x ≺ y = x ∙ s ≤ y

    infix 4 _≺_
    _≺_ : 𝑆 → 𝑆 → Type _
    x ≺ y = ∃ k × (y ≡ x ∙ k) × (k ≢ ε)

    mon-well-founded : Type _
    mon-well-founded = ∀ s → s ≢ ε → WellFounded [ s ]_≺_

  -- Total Antisymmetric POM
  record TAPOM ℓ₂ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
    field pom : POM ℓ₂
    open POM pom public using (preorder; _≤_; ≤-cong; ≤-congʳ; x≤x∙y; commutativeMonoid; positive)
    open CommutativeMonoid commutativeMonoid public
    field
      _≤|≥_   : Total _≤_
      antisym : Antisymmetric _≤_

    totalOrder : TotalOrder 𝑆 ℓ₂ ℓ₂
    totalOrder = fromPartialOrder (record { preorder = preorder ; antisym = antisym }) _≤|≥_
    open TotalOrder totalOrder public hiding (_≤|≥_; antisym) renaming (refl to ≤-refl)

    ⟨⊓⟩∙ : _∙_ Distributesˡ _⊓_ ,⦂ (∀ x y z → (x ⊓ y) ∙ z  ≡ (x ∙ z) ⊓ (y ∙ z))
    ⟨⊓⟩∙ x y z with x <? y | (x ∙ z) <? (y ∙ z)
    ... | yes x<y | yes xz<yz = refl
    ... | no  x≮y | no  xz≮yz = refl
    ... | no  x≮y | yes xz<yz = absurd (<⇒≱ xz<yz (≤-congʳ z (≮⇒≥ x≮y)))
    ... | yes x<y | no  xz≮yz = antisym (≤-congʳ z (<⇒≤ x<y)) (≮⇒≥ xz≮yz)

    ∙⟨⊓⟩ : _∙_ Distributesʳ _⊓_ ,⦂ (∀ x y z → x ∙ (y ⊓ z)  ≡ (x ∙ y) ⊓ (x ∙ z))
    ∙⟨⊓⟩ x y z = comm x (y ⊓ z) ; ⟨⊓⟩∙ y z x ; cong₂ _⊓_ (comm y x) (comm z x)

    <-cancelˡ : ∀ x {y z} → x ∙ y < x ∙ z → y < z
    <-cancelˡ x x∙y<x∙z y≤z = x∙y<x∙z (≤-cong x y≤z)

    <-cancelʳ : ∀ {x y} z → x ∙ z < y ∙ z → x < y
    <-cancelʳ z x∙z<y∙z x≤y = x∙z<y∙z (≤-congʳ z x≤y)

  -- Every commutative monoid generates a positively ordered monoid
  -- called the "algebraic" or "minimal" pom
  module AlgebraicPOM (mon : CommutativeMonoid 𝑆) where
    commutativeMonoid = mon
    open CommutativeMonoid mon

    infix 4 _≤_
    _≤_ : 𝑆 → 𝑆 → Type-
\end{code}
%<*algebraic-preorder>
\begin{code}
    x ≤ y = ∃ z × (y ≡ x ∙ z)
\end{code}
%</algebraic-preorder>
\begin{code}

    -- The snd here is the same proof as alg-≤-trans, so could be refactored out.
    ≤-trans : Transitive _≤_
    ≤-trans (k₁ , _) (k₂ , _) .fst = k₁ ∙ k₂
    ≤-trans {x} {y} {z} (k₁ , y≡x∙k₁) (k₂ , z≡y∙k₂) .snd =
      z             ≡⟨ z≡y∙k₂ ⟩
      y ∙ k₂        ≡⟨ cong (_∙ k₂) y≡x∙k₁ ⟩
      (x ∙ k₁) ∙ k₂ ≡⟨ assoc x k₁ k₂ ⟩
      x ∙ (k₁ ∙ k₂) ∎

    preorder : Preorder 𝑆 ℓ₁
    Preorder._≤_ preorder = _≤_
    Preorder.refl preorder = ε , sym (∙ε _)
    Preorder.trans preorder = ≤-trans

    positive : ∀ x → ε ≤ x
    positive x = x , sym (ε∙ x)

    ≤-cong : ∀ x {y z} → y ≤ z → x ∙ y ≤ x ∙ z
    ≤-cong x (k , z≡y∙k) = k , (cong (x ∙_) z≡y∙k ; sym (assoc x _ k))

  algebraic-pom : CommutativeMonoid 𝑆 → POM ℓ₁
  algebraic-pom mon = record { AlgebraicPOM mon }

  -- Total Minimal POM
  record TMPOM : Type ℓ₁ where
    field commutativeMonoid : CommutativeMonoid 𝑆

    pom : POM _
    pom = algebraic-pom commutativeMonoid

    open POM pom public

    infix 4 _≤|≥_
    field
\end{code}
%<*preorder-total>
\begin{code}
      _≤|≥_ : ∀ x y → (x ≤ y) ⊎ (y ≤ x)
\end{code}
%</preorder-total>
\begin{code}

    <⇒≺ : ∀ x y → y ≰ x → x ≺ y
    <⇒≺ x y x<y with x ≤|≥ y
    ... | inr y≤x = absurd (x<y y≤x)
    ... | inl (k , y≡x∙k) = λ
      where
      .fst → k
      .snd .fst → y≡x∙k
      .snd .snd k≡ε → x<y (ε , sym (∙ε y ; y≡x∙k ; cong (x ∙_) k≡ε ; ∙ε x))

    infixl 6 _∸_
    _∸_ : 𝑆 → 𝑆 → 𝑆
\end{code}
%<*monus-impl>
\begin{code}
    x ∸ y = (const ε ▿ fst) (x ≤|≥ y)
\end{code}
%</monus-impl>
\begin{code}

    x∸y≤x : ∀ x y → x ∸ y ≤ x
    x∸y≤x x y with x ≤|≥ y
    ... | inl (k , p) = positive x
    ... | inr (k , x≡y∙k) = y , (x≡y∙k ; comm y k)

  -- Total Minimal Antisymmetric POM
  record TMAPOM : Type ℓ₁ where
    field tmpom : TMPOM
    open TMPOM tmpom
      public
      using
        ( _≤_
        ; _≤|≥_
        ; positive
        ; alg-≤-trans
        ; _≺_
        ; <⇒≺
        ; _∸_
        ; x∸y≤x
        ; [_]_≺_
        ; mon-well-founded
        )
    field antisym : Antisymmetric _≤_

    tapom : TAPOM ℓ₁
    TAPOM.pom tapom = TMPOM.pom tmpom
    TAPOM._≤|≥_ tapom = _≤|≥_
    TAPOM.antisym tapom = antisym

    open TAPOM tapom public hiding (antisym; _≤|≥_; _≤_; positive)

    zeroSumFree : ∀ x y → x ∙ y ≡ ε → x ≡ ε
    zeroSumFree x y x∙y≡ε = antisym (y , sym x∙y≡ε) (positive x)

    ≤‿∸‿cancel : ∀ x y → x ≤ y → (y ∸ x) ∙ x ≡ y
    ≤‿∸‿cancel x y x≤y with y ≤|≥ x
    ... | inl y≤x = ε∙ x ; antisym x≤y y≤x
    ... | inr (k , y≡x∙k) = comm k x ; sym y≡x∙k

    ∸‿comm : ∀ x y → x ∙ (y ∸ x) ≡ y ∙ (x ∸ y)
    ∸‿comm x y with y ≤|≥ x | x ≤|≥ y
    ... | inl y≤x | inl x≤y = cong (_∙ ε) (antisym x≤y y≤x)
    ... | inr (k , y≡x∙k) | inl x≤y = sym y≡x∙k ; sym (∙ε y)
    ... | inl y≤x | inr (k , x≥y) = ∙ε x ; x≥y
    ... | inr (k₁ , y≡x∙k₁) | inr (k₂ , x≡y∙k₂) =
      x ∙ k₁ ≡˘⟨ y≡x∙k₁ ⟩
      y      ≡⟨ antisym  (k₂ , x≡y∙k₂) (k₁ , y≡x∙k₁) ⟩
      x      ≡⟨ x≡y∙k₂ ⟩
      y ∙ k₂ ∎

    ∸‿≺ : ∀ x y → x ≢ ε → y ≢ ε → x ∸ y ≺ x
    ∸‿≺ x y x≢ε y≢ε with x ≤|≥ y
    ... | inl _ = x , sym (ε∙ x) , x≢ε
    ... | inr (k , x≡y∙k) = y , (x≡y∙k ; comm y k) , y≢ε

    ≤-[]≺-trans : ∀ {s₁ s₂ x y} → s₁ ≤ s₂ → [ s₂ ] x ≺ y → [ s₁ ] x ≺ y
    ≤-[]≺-trans (k₁ , p₁) (k₂ , p₂) .fst = k₁ ∙ k₂
    ≤-[]≺-trans {s₁ = s₁} {s₂ = s₂} {x = x} {y = y} (k₁ , p₁) (k₂ , p₂) .snd =
      y ≡⟨ p₂ ⟩
      (x ∙ s₂) ∙ k₂ ≡⟨ assoc x s₂ k₂ ⟩
      x ∙ (s₂ ∙ k₂) ≡⟨ cong (x ∙_) (cong (_∙ k₂) p₁) ⟩
      x ∙ ((s₁ ∙ k₁) ∙ k₂) ≡⟨ cong (x ∙_) (assoc s₁ k₁ k₂) ⟩
      x ∙ (s₁ ∙ (k₁ ∙ k₂)) ≡˘⟨ assoc x s₁ (k₁ ∙ k₂) ⟩
      (x ∙ s₁) ∙ (k₁ ∙ k₂) ∎

    []≺-≤-trans : ∀ {s x y z} → [ s ] x ≺ y → y ≤ z → [ s ] x ≺ z
    []≺-≤-trans (k₁ , p₁) (k₂ , p₂) .fst = k₁ ∙ k₂
    []≺-≤-trans {s = s} {x = x} {y = y} {z = z} (k₁ , p₁) (k₂ , p₂) .snd =
      z ≡⟨ p₂ ⟩
      y ∙ k₂ ≡⟨ cong (_∙ k₂) p₁ ⟩
      ((x ∙ s) ∙ k₁) ∙ k₂ ≡⟨ assoc (x ∙ s) k₁ k₂ ⟩
      (x ∙ s) ∙ (k₁ ∙ k₂) ∎
    
    [_]_≺?_ : ∀ s x y → Dec ([ s ] x ≺ y)
    [ s ] x ≺? y = x ∙ s ≤? y

  -- Commutative Monoids with Monus
  record CMM : Type ℓ₁ where
    field commutativeMonoid : CommutativeMonoid 𝑆

    pom : POM _
    pom = algebraic-pom commutativeMonoid

    open POM pom public

    field _∸_ : 𝑆 → 𝑆 → 𝑆
    infixl 6 _∸_
    field
      ∸‿comm  : ∀ x y → x ∙ (y ∸ x) ≡ y ∙ (x ∸ y)
      ∸‿assoc : ∀ x y z → (x ∸ y) ∸ z ≡ x ∸ (y ∙ z)
      ∸‿inv   : ∀ x → x ∸ x ≡ ε
      ε∸      : ∀ x → ε ∸ x ≡ ε

    ∸ε : ∀ x → x ∸ ε ≡ x
    ∸ε x =
      x ∸ ε       ≡˘⟨ ε∙ (x ∸ ε) ⟩
      ε ∙ (x ∸ ε) ≡⟨ ∸‿comm ε x ⟩
      x ∙ (ε ∸ x) ≡⟨ cong (x ∙_) (ε∸ x) ⟩
      x ∙ ε       ≡⟨ ∙ε x ⟩
      x ∎

    ∸≤ : ∀ x y → x ≤ y → x ∸ y ≡ ε
    ∸≤ x y (k , y≡x∙k) =
      x ∸ y       ≡⟨ cong (x ∸_) y≡x∙k ⟩
      x ∸ (x ∙ k) ≡˘⟨ ∸‿assoc x x k ⟩
      (x ∸ x) ∸ k ≡⟨ cong (_∸ k) (∸‿inv x) ⟩
      ε ∸ k       ≡⟨ ε∸ k ⟩
      ε ∎

    ∣_-_∣ : 𝑆 → 𝑆 → 𝑆
    ∣ x - y ∣ = (x ∸ y) ∙ (y ∸ x)

    _⊔₂_ : 𝑆 → 𝑆 → 𝑆
    x ⊔₂ y = x ∙ y ∙ ∣ x - y ∣

    _⊓₂_ : 𝑆 → 𝑆 → 𝑆
    x ⊓₂ y = (x ∙ y) ∸ ∣ x - y ∣


  -- Cancellative Commutative Monoids with Monus
  record CCMM : Type ℓ₁ where
    field cmm : CMM
    open CMM cmm public

    field ∸‿cancel : ∀ x y → (x ∙ y) ∸ x ≡ y

    cancelˡ : Cancellativeˡ _∙_
    cancelˡ x y z x∙y≡x∙z =
      y           ≡˘⟨ ∸‿cancel x y ⟩
      (x ∙ y) ∸ x ≡⟨ cong (_∸ x) x∙y≡x∙z ⟩
      (x ∙ z) ∸ x ≡⟨ ∸‿cancel x z ⟩
      z ∎

    cancelʳ : Cancellativeʳ _∙_
    cancelʳ x y z y∙x≡z∙x =
      y           ≡˘⟨ ∸‿cancel x y ⟩
      (x ∙ y) ∸ x ≡⟨ cong (_∸ x) (comm x y) ⟩
      (y ∙ x) ∸ x ≡⟨ cong (_∸ x) y∙x≡z∙x ⟩
      (z ∙ x) ∸ x ≡⟨ cong (_∸ x) (comm z x) ⟩
      (x ∙ z) ∸ x ≡⟨ ∸‿cancel x z ⟩
      z ∎

    zeroSumFree : ∀ x y → x ∙ y ≡ ε → x ≡ ε
    zeroSumFree x y x∙y≡ε =
      x           ≡˘⟨ ∸‿cancel y x ⟩
      (y ∙ x) ∸ y ≡⟨ cong (_∸ y) (comm y x) ⟩
      (x ∙ y) ∸ y ≡⟨ cong (_∸ y) x∙y≡ε ⟩
      ε ∸ y       ≡⟨ ε∸ y ⟩
      ε ∎

    antisym : Antisymmetric _≤_
    antisym {x} {y} (k₁ , y≡x∙k₁) (k₂ , x≡y∙k₂) =
        x      ≡⟨ x≡y∙k₂ ⟩
        y ∙ k₂ ≡⟨ [ lemma                 ]⇒ y ∙ ε   ≡ y ∙ (k₂ ∙ k₁)
                  ⟨ cancelˡ y ε (k₂ ∙ k₁) ⟩⇒ ε       ≡ k₂ ∙ k₁
                  ⟨ sym                   ⟩⇒ k₂ ∙ k₁ ≡ ε
                  ⟨ zeroSumFree k₂ k₁     ⟩⇒ k₂      ≡ ε
                  ⟨ cong (y ∙_)           ⟩⇒ y ∙ k₂  ≡ y ∙ ε ⇒∎ ⟩
        y ∙ ε  ≡⟨ ∙ε y ⟩
        y ∎
      where
      lemma = ∙ε y ; alg-≤-trans x≡y∙k₂ y≡x∙k₁

    partialOrder : PartialOrder _ _
    PartialOrder.preorder partialOrder = preorder
    PartialOrder.antisym partialOrder = antisym

    ≺⇒< : ∀ x y → x ≺ y → y ≰ x
    ≺⇒< x y (k₁ , y≡x∙k₁ , k₁≢ε) (k₂ , x≡y∙k₂) =
      [ x ∙ ε         ≡⟨ ∙ε x ⟩
        x             ≡⟨ x≡y∙k₂ ⟩
        y ∙ k₂        ≡⟨ cong (_∙ k₂) y≡x∙k₁ ⟩
        (x ∙ k₁) ∙ k₂ ≡⟨ assoc x k₁ k₂ ⟩
        x ∙ (k₁ ∙ k₂) ∎       ]⇒ x ∙ ε ≡ x ∙ (k₁ ∙ k₂)
      ⟨ cancelˡ x ε (k₁ ∙ k₂) ⟩⇒ ε ≡ k₁ ∙ k₂
      ⟨ sym                   ⟩⇒ k₁ ∙ k₂ ≡ ε
      ⟨ zeroSumFree k₁ k₂     ⟩⇒ k₁ ≡ ε
      ⟨ k₁≢ε                  ⟩⇒ ⊥ ⇒∎

    ≤⇒<⇒≢ε : ∀ x y → (x≤y : x ≤ y) → y ≰ x → fst x≤y ≢ ε
    ≤⇒<⇒≢ε x y (k₁ , y≡x∙k₁) y≰x k₁≡ε = y≰x λ
      where
      .fst → ε
      .snd → x      ≡˘⟨ ∙ε x ⟩
            x ∙ ε  ≡˘⟨ cong (x ∙_) k₁≡ε ⟩
            x ∙ k₁ ≡˘⟨ y≡x∙k₁ ⟩
            y      ≡˘⟨ ∙ε y ⟩ 
            y ∙ ε ∎

    ≤-cancelʳ : ∀ x y z → y ∙ x ≤ z ∙ x → y ≤ z
    ≤-cancelʳ x y z (k , z∙x≡y∙x∙k) .fst = k
    ≤-cancelʳ x y z (k , z∙x≡y∙x∙k) .snd = cancelʳ x z (y ∙ k) $
      z ∙ x ≡⟨ z∙x≡y∙x∙k ⟩
      (y ∙ x) ∙ k ≡⟨ assoc y x k ⟩
      y ∙ (x ∙ k) ≡⟨ cong (y ∙_) (comm x k) ⟩
      y ∙ (k ∙ x) ≡˘⟨ assoc y k x ⟩
      (y ∙ k) ∙ x ∎

    ≤-cancelˡ : ∀ x y z → x ∙ y ≤ x ∙ z → y ≤ z
    ≤-cancelˡ x y z (k , x∙z≡x∙y∙k) .fst = k
    ≤-cancelˡ x y z (k , x∙z≡x∙y∙k) .snd =
      cancelˡ x z (y ∙ k) (x∙z≡x∙y∙k ; assoc x y k)

    <-congˡ : ∀ x {y z} → ¬ (z ≤ y) → ¬ (x ∙ z ≤ x ∙ y)
    <-congˡ x y<z x∙z≤x∙y = y<z (≤-cancelˡ x _ _ x∙z≤x∙y)

    <-congʳ : ∀ x {y z} → ¬ (z ≤ y) → ¬ (z ∙ x ≤ y ∙ x)
    <-congʳ x y<z x∙z≤x∙y = y<z (≤-cancelʳ x _ _ x∙z≤x∙y)

    ≺-irrefl : Irreflexive _≺_
    ≺-irrefl {x} (k , x≡x∙k , k≢ε) = k≢ε (sym (cancelˡ x ε k (∙ε x ; x≡x∙k)))

    ≤∸ : ∀ x y → (x≤y : x ≤ y) → y ∸ x ≡ fst x≤y
    ≤∸ x y (k , y≡x∙k) =
      y ∸ x       ≡⟨ cong (_∸ x) y≡x∙k ⟩
      (x ∙ k) ∸ x ≡⟨ ∸‿cancel x k ⟩
      k ∎

    ≤‿∸‿cancel : ∀ x y → x ≤ y → (y ∸ x) ∙ x ≡ y
    ≤‿∸‿cancel x y (k , y≡x∙k) =
      (y ∸ x) ∙ x ≡⟨ cong (λ y → (y ∸ x) ∙ x) y≡x∙k ⟩
      ((x ∙ k) ∸ x) ∙ x ≡⟨ cong (_∙ x) (∸‿cancel x k) ⟩
      k ∙ x ≡⟨ comm k x ⟩
      x ∙ k ≡˘⟨ y≡x∙k ⟩
      y ∎

  -- Cancellative total minimal antisymmetric pom (has monus)
  record CTMAPOM : Type ℓ₁ where
    field tmapom : TMAPOM
    open TMAPOM tmapom public
    field cancel : Cancellativeˡ _∙_

    module cmm where
      ∸≤ : ∀ x y → x ≤ y → x ∸ y ≡ ε
      ∸≤ x y x≤y with x ≤|≥ y
      ∸≤ x y x≤y | inl _ = refl
      ∸≤ x y (k₁ , y≡x∙k₁) | inr (k₂ , x≡y∙k₂) =
        [ lemma                ]⇒ y ∙ ε   ≡ y ∙ (k₂ ∙ k₁)
        ⟨ cancel y ε (k₂ ∙ k₁) ⟩⇒ ε       ≡ k₂ ∙ k₁
        ⟨ sym                  ⟩⇒ k₂ ∙ k₁ ≡ ε
        ⟨ zeroSumFree k₂ k₁    ⟩⇒ k₂      ≡ ε ⇒∎
        where
        lemma = ∙ε y ; alg-≤-trans x≡y∙k₂ y≡x∙k₁

      ∸‿inv : ∀ x → x ∸ x ≡ ε
      ∸‿inv x = ∸≤ x x ≤-refl

      ε∸ : ∀ x → ε ∸ x ≡ ε
      ε∸ x = ∸≤ ε x (positive x)

      ∸‿assoc : ∀ x y z → (x ∸ y) ∸ z ≡ x ∸ (y ∙ z)
      ∸‿assoc x y z with x ≤|≥ y
      ∸‿assoc x y z | inl x≤y  = ε∸ z ; sym (∸≤ x (y ∙ z) (≤-trans x≤y x≤x∙y))
      ∸‿assoc x y z | inr x≥y with x ≤|≥ y ∙ z
      ∸‿assoc x y z | inr (k₁ , x≡y∙k₁) | inl (k₂ , y∙z≡x∙k₂) = ∸≤ k₁ z (k₂ , lemma)
        where
        lemma : z ≡ k₁ ∙ k₂
        lemma = cancel y z (k₁ ∙ k₂) (alg-≤-trans x≡y∙k₁ y∙z≡x∙k₂)

      ∸‿assoc x y z | inr (k , x≡y∙k) | inr x≥y∙z with k ≤|≥ z
      ∸‿assoc x y z | inr (k₁ , x≡y∙k₁) | inr (k₂ , x≡y∙z∙k₂) | inl (k₃ , z≡k₁∙k₃) =
          [ lemma₁            ]⇒ ε       ≡ k₂ ∙ k₃
          ⟨ sym               ⟩⇒ k₂ ∙ k₃ ≡ ε
          ⟨ zeroSumFree k₂ k₃ ⟩⇒ k₂      ≡ ε
          ⟨ sym               ⟩⇒ ε       ≡ k₂ ⇒∎
        where
        lemma₃ =
          y ∙ k₁       ≡˘⟨ x≡y∙k₁ ⟩
          x            ≡⟨ x≡y∙z∙k₂ ⟩
          (y ∙ z) ∙ k₂ ≡⟨ assoc y z k₂ ⟩
          y ∙ (z ∙ k₂) ∎

        lemma₂ =
          k₁ ∙ ε         ≡⟨ ∙ε k₁ ⟩
          k₁             ≡⟨ alg-≤-trans z≡k₁∙k₃ (cancel y k₁ (z ∙ k₂) lemma₃) ⟩
          k₁ ∙ (k₃ ∙ k₂) ∎

        lemma₁ =
          ε       ≡⟨ cancel k₁ ε (k₃ ∙ k₂) lemma₂ ⟩
          k₃ ∙ k₂ ≡⟨ comm k₃ k₂ ⟩
          k₂ ∙ k₃ ∎

      ∸‿assoc x y z | inr (k₁ , x≡y∙k₁) | inr (k₂ , x≡y∙z∙k₂) | inr (k₃ , k₁≡z∙k₃) =
          cancel z k₃ k₂ lemma₂
        where
        lemma₁ =
          y ∙ k₁       ≡˘⟨ x≡y∙k₁ ⟩
          x            ≡⟨ x≡y∙z∙k₂ ⟩
          (y ∙ z) ∙ k₂ ≡⟨ assoc y z k₂ ⟩
          y ∙ (z ∙ k₂) ∎

        lemma₂ =
          z ∙ k₃ ≡˘⟨ k₁≡z∙k₃ ⟩
          k₁     ≡⟨ cancel y k₁ (z ∙ k₂) lemma₁ ⟩
          z ∙ k₂ ∎

    open cmm public

    ∸‿cancel : ∀ x y → (x ∙ y) ∸ x ≡ y
    ∸‿cancel x y with (x ∙ y) ≤|≥ x
    ... | inl x∙y≤x = sym (cancel x y ε (antisym x∙y≤x x≤x∙y ; sym (∙ε x)))
    ... | inr (k , x∙y≡x∙k) = sym (cancel x y k x∙y≡x∙k)

    ccmm : CCMM
    ccmm = record { ∸‿cancel = ∸‿cancel
                  ; cmm = record { cmm
                                ; ∸‿comm = ∸‿comm
                                ; commutativeMonoid = commutativeMonoid } }

    open CCMM ccmm public
      using (cancelʳ; cancelˡ; ∸ε; ≺⇒<; ≤⇒<⇒≢ε; _⊔₂_; _⊓₂_; ≺-irrefl; ≤∸; ≤-cancelˡ; ≤-cancelʳ; <-congˡ; <-congʳ)

    ∸‿< : ∀ x y → x ≢ ε → y ≢ ε → x ∸ y < x
    ∸‿< x y x≢ε y≢ε = ≺⇒< (x ∸ y) x (∸‿≺ x y x≢ε y≢ε)

    ∸‿<-< : ∀ x y → x < y → x ≢ ε → y ∸ x < y
    ∸‿<-< x y x<y x≢ε = ∸‿< y x (λ y≡ε → x<y (x , sym (cong (_∙ x) y≡ε ; ε∙ x))) x≢ε

    2× : 𝑆 → 𝑆
    2× x = x ∙ x

    double-max : ∀ x y → 2× (x ⊔ y) ≡ x ⊔₂ y
    double-max x y with x ≤|≥ y | y ≤|≥ x
    double-max x y | inl x≤y | inl y≤x =
      x ∙ x ≡⟨ cong (x ∙_) (antisym x≤y y≤x) ⟩
      x ∙ y ≡˘⟨ ∙ε (x ∙ y) ⟩
      (x ∙ y) ∙ ε ≡˘⟨ cong ((x ∙ y) ∙_)  (ε∙ ε) ⟩
      (x ∙ y) ∙ (ε ∙ ε) ∎
    double-max x y | inl x≤y | inr (k , y≡x∙k) =
      y ∙ y ≡⟨ cong (y ∙_) y≡x∙k ⟩
      y ∙ (x ∙ k) ≡˘⟨ assoc y x k ⟩
      (y ∙ x) ∙ k ≡⟨ cong (_∙ k) (comm y x) ⟩
      (x ∙ y) ∙ k ≡˘⟨ cong ((x ∙ y) ∙_) (ε∙ k) ⟩
      (x ∙ y) ∙ (ε ∙ k) ∎
    double-max x y | inr (k , x≡y∙k) | inl y≤x =
      x ∙ x ≡⟨ cong (x ∙_) x≡y∙k ⟩
      x ∙ (y ∙ k) ≡˘⟨ assoc x y k ⟩
      (x ∙ y) ∙ k ≡˘⟨ cong ((x ∙ y) ∙_) (∙ε k) ⟩
      (x ∙ y) ∙ (k ∙ ε) ∎
    double-max x y | inr (k₁ , x≡y∙k₁) | inr (k₂ , y≡x∙k₂) =
      x ∙ x ≡⟨ cong (x ∙_) (antisym (k₂ , y≡x∙k₂) (k₁ , x≡y∙k₁)) ⟩
      x ∙ y ≡⟨ cong₂ _∙_ x≡y∙k₁ y≡x∙k₂ ⟩
      (y ∙ k₁) ∙ (x ∙ k₂) ≡˘⟨ assoc (y ∙ k₁) x k₂ ⟩
      ((y ∙ k₁) ∙ x) ∙ k₂ ≡⟨ cong (_∙ k₂) (comm (y ∙ k₁) x) ⟩
      (x ∙ (y ∙ k₁)) ∙ k₂ ≡˘⟨ cong (_∙ k₂) (assoc x y k₁) ⟩
      ((x ∙ y) ∙ k₁) ∙ k₂ ≡⟨ assoc (x ∙ y) k₁ k₂ ⟩
      (x ∙ y) ∙ (k₁ ∙ k₂) ∎

    open import Data.Sigma.Properties

    ≤-prop : ∀ x y → isProp (x ≤ y)
    ≤-prop x y (k₁ , y≡x∙k₁) (k₂ , y≡x∙k₂) = Σ≡Prop (λ _ → total⇒isSet _ _) (cancelˡ x k₁ k₂ (sym y≡x∙k₁ ; y≡x∙k₂))

    open import Cubical.Foundations.HLevels using (isProp×)
    open import Data.Empty.Properties using (isProp¬)

    ≺-prop : ∀ x y → isProp (x ≺ y)
    ≺-prop x y (k₁ , y≡x∙k₁ , k₁≢ε) (k₂ , y≡x∙k₂ , k₂≢ε) = Σ≡Prop (λ k → isProp× (total⇒isSet _ _) isProp¬) (cancelˡ x k₁ k₂ (sym y≡x∙k₁ ; y≡x∙k₂))

  record WellFoundedMonus : Type ℓ₁ where
    field ctmapom : CTMAPOM
    open CTMAPOM ctmapom public
    Step : Type ℓ₁
\end{code}
%<*step>
\begin{code}
    Step = ∃ s × s ≢ ε
\end{code}
%</step>
\begin{code}
    field well-founded : (s : Step) → WellFounded [ s .fst ]_≺_

  record StrictWellFoundedMonus : Type ℓ₁ where
    field ctmapom : CTMAPOM
    open CTMAPOM ctmapom public
    field well-founded : WellFounded _≺_

  module MonusWeight {ℓ₂} (tapom : TAPOM ℓ₂) where
    open TAPOM tapom

    _⊕_ = _⊓_
    _⊗_ = _∙_
    𝟙 = ε
    ⊕-assoc = ⊓-assoc
    ⊕-com = ⊓-comm
    ⊗-assoc = assoc
    𝟙⊗ = ε∙
    ⊗𝟙 = ∙ε
    ⊗⟨⊕⟩ = ∙⟨⊓⟩
    ⟨⊕⟩⊗ = ⟨⊓⟩∙

  weight : ∀ {ℓ₂} → TAPOM ℓ₂ → Weight 𝑆
  weight tapom = record { MonusWeight tapom }
  -- We can construct the viterbi semiring by adjoining a top element to
  -- a tapom
  module Viterbi {ℓ₂} (tapom : TAPOM ℓ₂) where
    open TAPOM tapom
    open import Relation.Binary.Construct.UpperBound totalOrder





    module ViterbiSemiring where
      𝑅 = ⌈∙⌉

      𝟘 𝟙 : 𝑅
      _⊗_ _⊕_ : 𝑅 → 𝑅 → 𝑅

      𝟙 = ⌈ ε ⌉

      ⌈⊤⌉   ⊗ y     = ⌈⊤⌉
      ⌈ x ⌉ ⊗ ⌈⊤⌉   = ⌈⊤⌉
      ⌈ x ⌉ ⊗ ⌈ y ⌉ = ⌈ x ∙ y ⌉

      𝟘 = ⌈⊤⌉

      ⌈⊤⌉   ⊕ y     = y
      ⌈ x ⌉ ⊕ ⌈⊤⌉   = ⌈ x ⌉
      ⌈ x ⌉ ⊕ ⌈ y ⌉ = ⌈ x ⊓ y ⌉

      ⊗-assoc : Associative _⊗_
      ⊗-assoc ⌈⊤⌉   _     _     = refl
      ⊗-assoc ⌈ _ ⌉ ⌈⊤⌉   _     = refl
      ⊗-assoc ⌈ _ ⌉ ⌈ _ ⌉ ⌈⊤⌉   = refl
      ⊗-assoc ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ = cong ⌈_⌉ (assoc x y z)

      ⊗-com : Commutative _⊗_
      ⊗-com ⌈⊤⌉   ⌈⊤⌉   = refl
      ⊗-com ⌈⊤⌉   ⌈ _ ⌉ = refl
      ⊗-com ⌈ _ ⌉ ⌈⊤⌉   = refl
      ⊗-com ⌈ x ⌉ ⌈ y ⌉ = cong ⌈_⌉ (comm x y)

      ⟨⊕⟩⊗ : _⊗_ Distributesˡ _⊕_
      ⟨⊕⟩⊗ ⌈⊤⌉   _     _     = refl
      ⟨⊕⟩⊗ ⌈ _ ⌉ ⌈⊤⌉   ⌈⊤⌉   = refl
      ⟨⊕⟩⊗ ⌈ _ ⌉ ⌈⊤⌉   ⌈ _ ⌉ = refl
      ⟨⊕⟩⊗ ⌈ x ⌉ ⌈ y ⌉ ⌈⊤⌉   = refl
      ⟨⊕⟩⊗ ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ = cong ⌈_⌉ (⟨⊓⟩∙ x y z)

      ⊕-assoc : Associative _⊕_
      ⊕-assoc ⌈⊤⌉   _     _     = refl
      ⊕-assoc ⌈ x ⌉ ⌈⊤⌉   _     = refl
      ⊕-assoc ⌈ x ⌉ ⌈ _ ⌉ ⌈⊤⌉   = refl
      ⊕-assoc ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ = cong ⌈_⌉ (⊓-assoc x y z)

      𝟘⊕ : ∀ x → 𝟘 ⊕ x ≡ x
      𝟘⊕ ⌈⊤⌉   = refl
      𝟘⊕ ⌈ _ ⌉ = refl

      -- ⊕0 : ∀ x → x ⊕ 𝟘 ≡ x
      -- ⊕0 ⌈ _ ⌉ = refl
      -- ⊕0 ⌈⊤⌉   = refl

      𝟙⊗ : ∀ x → 𝟙 ⊗ x ≡ x
      𝟙⊗ ⌈⊤⌉   = refl
      𝟙⊗ ⌈ x ⌉ = cong ⌈_⌉ (ε∙ x)

      ⊗𝟙 : ∀ x → x ⊗ 𝟙 ≡ x
      ⊗𝟙 ⌈⊤⌉   = refl
      ⊗𝟙 ⌈ x ⌉ = cong ⌈_⌉ (∙ε x)

      𝟘⊗ : ∀ x → 𝟘 ⊗ x ≡ 𝟘
      𝟘⊗ _ = refl

      ⊕-com : Commutative _⊕_
      ⊕-com ⌈⊤⌉   ⌈⊤⌉   = refl
      ⊕-com ⌈⊤⌉   ⌈ _ ⌉ = refl
      ⊕-com ⌈ _ ⌉ ⌈⊤⌉   = refl
      ⊕-com ⌈ x ⌉ ⌈ y ⌉ = cong ⌈_⌉ (⊓-comm x y)

      ⊗𝟘 : ∀ x → x ⊗ ⌈⊤⌉ ≡ ⌈⊤⌉
      ⊗𝟘 ⌈ _ ⌉ = refl
      ⊗𝟘 ⌈⊤⌉   = refl

      ⊗⟨⊕⟩ : _⊗_ Distributesʳ _⊕_
      ⊗⟨⊕⟩ x y z = ⊗-com x (y ⊕ z) ; ⟨⊕⟩⊗ y z x ; cong₂ _⊕_ (⊗-com y x) (⊗-com z x)


    viterbi : Semiring _
    viterbi = record { ViterbiSemiring }

  open Viterbi using (viterbi) public

  -- viterbi : ∀ {ℓ₂} → TAPOM ℓ₂ → Semiring (Maybe 𝑆)
  -- viterbi tapom = record { Viterbi tapom }

\end{code}
