{-# OPTIONS --safe #-}

module Data.Nat.Monus where

open import Prelude
open import Data.Nat
open import Data.Nat.Properties
open import Algebra.Monus
open import Algebra
open import Agda.Builtin.Nat using (_+_)

-- +-assoc : Associative _+_
-- +-assoc zero y z = refl
-- +-assoc (suc x) y z = cong suc (+-assoc x y z)

+0 : ∀ n → n + 0 ≡ n
+0 zero = refl
+0 (suc n) = cong suc (+0 n)

-- +-suc : ∀ n m → n + suc m ≡ suc (n + m)
-- +-suc zero m = refl
-- +-suc (suc n) m = cong suc (+-suc n m)

-- +-comm : ∀ n m → n + m ≡ m + n
-- +-comm zero m = sym (+0 m)
-- +-comm (suc n) m = cong suc (+-comm n m) ; sym (+-suc m n)

+-cancel : Cancellativeˡ _+_
+-cancel zero y z p = p
+-cancel (suc x) y z p = +-cancel x y z (suc-inj p)

cmp : ∀ n m → (∃ k × m ≡ n + k) ⊎ (∃ k × n ≡ m + k)
cmp zero m = inl (m , refl)
cmp n zero = inr (n , refl)
cmp (suc n) (suc m) = map-⊎ (map₂ (cong suc)) (map₂ (cong suc)) (cmp n m)

-- pred : ℕ → ℕ
-- pred (suc n) = n
-- pred n = n

asm : ∀ n m → (∃ k × m ≡ n + k) → (∃ k × n ≡ m + k) → n ≡ m
asm zero zero p q = refl
asm zero (suc m) p (_ , q) = absurd (zero≢suc q)
asm (suc n) zero (_ , p) q = absurd (zero≢suc p)
asm (suc n) (suc m) (k₁ , p) (k₂ , q) = cong suc (asm n m (k₁ , cong pred p) (k₂ , cong pred q))

nat-mon : TMAPOM ℕ
nat-mon .TMAPOM.tmpom .TMPOM.commutativeMonoid .CommutativeMonoid.monoid .Monoid._∙_ = _+_
nat-mon .TMAPOM.tmpom .TMPOM.commutativeMonoid .CommutativeMonoid.monoid .Monoid.ε = 0
nat-mon .TMAPOM.tmpom .TMPOM.commutativeMonoid .CommutativeMonoid.monoid .Monoid.assoc = +-assoc
nat-mon .TMAPOM.tmpom .TMPOM.commutativeMonoid .CommutativeMonoid.monoid .Monoid.ε∙ _ = refl
nat-mon .TMAPOM.tmpom .TMPOM.commutativeMonoid .CommutativeMonoid.monoid .Monoid.∙ε = +0
nat-mon .TMAPOM.tmpom .TMPOM.commutativeMonoid .CommutativeMonoid.comm = +-comm
nat-mon .TMAPOM.tmpom .TMPOM._≤|≥_ = cmp
nat-mon .TMAPOM.antisym p q = asm _ _ p q

open TMAPOM nat-mon

wellFounded : mon-well-founded

module _ (s : ℕ) (s≢ε : s ≢ ε) where
  wellFounded′ : ∀ x y k → x ≡ suc k ∙ y → Acc [ s ]_≺_ y
  wellFounded′ zero    y zero p = absurd (zero≢suc p)
  wellFounded′ (suc x) y zero p = subst (Acc [ s ]_≺_) (cong pred p) (wellFounded s s≢ε x)
  wellFounded′ zero y (suc k) p = absurd (zero≢suc p)
  wellFounded′ (suc x) y (suc k) p = wellFounded′ x y k (cong pred p)

wellFounded zero s≢ε _ = absurd (s≢ε refl)
wellFounded (suc s) s≢ε x =
  acc (λ { y (k , p) → wellFounded′ (suc s) s≢ε x y (s ∙ k) (p ; assoc y (suc s) k ; comm y _) })

nat-wfmon : WellFoundedMonus ℕ
nat-wfmon .WellFoundedMonus.ctmapom .CTMAPOM.tmapom = nat-mon
nat-wfmon .WellFoundedMonus.ctmapom .CTMAPOM.cancel = +-cancel
nat-wfmon .WellFoundedMonus.well-founded = uncurry wellFounded
