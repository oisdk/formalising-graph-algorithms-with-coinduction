{-# OPTIONS --cubical --safe #-}

module Data.Nat.Properties where

open import Data.Nat
open import Agda.Builtin.Nat using () renaming (_<_ to _<ᴮ_) public
open import Prelude
open import Cubical.Data.Nat using (injSuc) public
open import Data.Unit

caseNat : ∀ {p} {P : ℕ → Type p} → P zero → (∀ {n} → P (suc n)) → ∀ x → P x
caseNat pz ps zero = pz
caseNat pz ps (suc n) = ps

infixr 4 _⊔_ _-1⊔_

_⊔_ _-1⊔_ : ℕ → ℕ → ℕ

zero  ⊔ m = m
suc n ⊔ m = suc (m -1⊔ n)

zero  -1⊔ n = n
suc m -1⊔ n = n ⊔ m

zero≢suc : ∀ {n} → zero ≢ suc n
zero≢suc z≡s = subst (caseNat ⊤ ⊥) z≡s tt

suc≢zero : ∀ {n} → suc n ≢ zero
suc≢zero s≡z = subst (caseNat ⊥ ⊤) s≡z tt

pred-may : ℕ → Maybe ℕ
pred-may = caseNat nothing (λ {n} → just n)

pred-or : ℕ → ℕ → ℕ
pred-or n = from-maybe n ∘ pred-may

pred : ℕ → ℕ
pred = pred-or zero

suc-inj : Injective suc
suc-inj = cong pred

+-inj : ∀ x {n m} → x + n ≡ x + m → n ≡ m
+-inj zero p = p
+-inj (suc x) p = +-inj x (suc-inj p)

open import Discrete

module Eqℕ where
  open import Agda.Builtin.Nat using () renaming (_==_ to _≡ᴮ_) public

  sound : ∀ n m →  T (n ≡ᴮ m) → n ≡ m
  sound zero zero p i = zero
  sound (suc n) (suc m) p i = suc (sound n m p i)

  complete : ∀ n → T (n ≡ᴮ n)
  complete zero = _
  complete (suc n) = complete n

open Eqℕ renaming (_≡ᴮ_ to _≡ᴺ_) public

discreteℕ : Discrete ℕ
discreteℕ = from-bool-eq (record { Eqℕ })

isSetNat : isSet ℕ
isSetNat = Discrete→isSet discreteℕ

+-suc : ∀ x y → x + suc y ≡ suc (x + y)
+-suc zero y = refl
+-suc (suc x) y = cong suc (+-suc x y)

+-idʳ : ∀ x → x + 0 ≡ x
+-idʳ zero     = refl
+-idʳ (suc x)  = cong suc (+-idʳ x)

+-comm : ∀ x y → x + y ≡ y + x
+-comm x zero = +-idʳ x
+-comm x (suc y) = +-suc x y ; cong suc (+-comm x y)

infix 4 _<_
_<_ : ℕ → ℕ → Type
n < m = T (n <ᴮ m)

infix 4 _≤ᴮ_
_≤ᴮ_ : ℕ → ℕ → Bool
n ≤ᴮ m = n <ᴮ suc m

infix 4 _≤_
_≤_ : ℕ → ℕ → Type
n ≤ m = T (n ≤ᴮ m)

<⇒≱ : ∀ x y → x < y → ¬ (y ≤ x)
<⇒≱ (suc x) (suc y) x<y y≤x = <⇒≱ x y x<y y≤x

<-suc : ∀ x → x < suc x
<-suc zero = tt
<-suc (suc x) = <-suc x

<-trans : ∀ x y z → x < y → y < z → x < z
<-trans zero    (suc y) (suc z) xy yz = tt
<-trans (suc x) (suc y) (suc z) xy yz = <-trans x y z xy yz

<-pred : ∀ x y → suc x < y → x < y
<-pred x y = <-trans x (suc x) y (<-suc x)

≤-refl : ∀ x → x ≤ x
≤-refl zero    = tt
≤-refl (suc x) = ≤-refl x

infix 4 _≥ᴮ_
_≥ᴮ_ : ℕ → ℕ → Bool
_≥ᴮ_ = flip _≤ᴮ_

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc zero     y z i = y + z
+-assoc (suc x)  y z i = suc (+-assoc x y z i)

-- +-*-distrib : ∀ x y z → (x + y) * z ≡ x * z + y * z
-- +-*-distrib zero y z = refl
-- +-*-distrib (suc x) y z = cong (z +_) (+-*-distrib x y z) ; sym (+-assoc z (x * z) (y * z))

-- *-zeroʳ : ∀ x → x * zero ≡ zero
-- *-zeroʳ zero = refl
-- *-zeroʳ (suc x) = *-zeroʳ x

-- *-suc : ∀ x y → x + x * y ≡ x * suc y
-- *-suc zero    y = refl
-- *-suc (suc x) y = cong suc (sym (+-assoc x y (x * y)) ; cong (_+ x * y) (+-comm x y) ; +-assoc y x (x * y) ; cong (y +_) (*-suc x y))

-- *-comm : ∀ x y → x * y ≡ y * x
-- *-comm zero    y = sym (*-zeroʳ y)
-- *-comm (suc x) y = cong (y +_) (*-comm x y) ; *-suc y x

-- *-assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
-- *-assoc zero    y z = refl
-- *-assoc (suc x) y z = +-*-distrib y (x * y) z ; cong (y * z +_) (*-assoc x y z)

x≢sx+y : ∀ x y → x ≢ suc x + y
x≢sx+y zero y = zero≢suc
x≢sx+y (suc x) y p = x≢sx+y x y (suc-inj p)

infix 4 _≤′_ _<′_

_≤′_ _<′_ : ℕ → ℕ → Type
n ≤′ m     = ∃ d × m ≡ d + n
n <′ m     = ∃ d × m ≡ suc d + n
{-# NOINLINE _≤′_ #-}
{-# NOINLINE _<′_ #-}

≤′-refl : ∀ x → x ≤′ x
≤′-refl _ = zero , refl

open import WellFounded

mutual
  <-wellFounded′ : ∀ n m → m <′ n → Acc _<′_ m
  <-wellFounded′ zero m (d , p) = absurd (zero≢suc p)
  <-wellFounded′ (suc n) m (zero  , m<n) = subst (Acc _<′_) (suc-inj m<n) (<-wellFounded n)
  <-wellFounded′ (suc n) m (suc d , m<n) = <-wellFounded′ n m (d , suc-inj m<n)

  <-wellFounded : WellFounded _<′_
  <-wellFounded n = acc (<-wellFounded′ n)

n≢sn : ∀ n → n ≢ suc n
n≢sn zero n≡sn = zero≢suc n≡sn
n≢sn (suc n) n≡sn = n≢sn n (suc-inj n≡sn)

n≢sm+n : ∀ n m → n ≢ n + suc m
n≢sm+n zero    m = zero≢suc
n≢sm+n (suc n) m = n≢sm+n n m ∘ suc-inj

<′⇒≢ : ∀ n m → n <′ m → n ≢ m
<′⇒≢ n m (d , p) n≡m = n≢sm+n m d (p ; +-comm (suc d) n ; cong (_+ suc d) n≡m)

isProp-<′ : ∀ n m → isProp (n <′ m)
isProp-≤′ : ∀ n m → isProp (n ≤′ m)

isProp-<′ n zero (d , p) = absurd (zero≢suc p)
isProp-<′ n (suc m) (d₁ , p₁) (d₂ , p₂) =
  let h = isProp-≤′ n m (d₁ , suc-inj p₁) (d₂ , suc-inj p₂)
  in Σ≡Prop (λ _ → isSetNat _ _) (cong fst h)

isProp-≤′ n m (d₁ , p₁) (d₂ , p₂) =
  Σ≡Prop (λ _ → isSetNat _ _) (+-inj n (+-comm n d₁ ; sym p₁ ; p₂ ; +-comm d₂ n))

s≤⇒< : ∀ n m → suc n ≤′ m → n <′ m
s≤⇒< n m (d , p) = d , (p ; +-suc d n)

≤⇒s< : ∀ n m → n ≤′ m → n <′ suc m
≤⇒s< _ _ = map₂ (cong suc)

<⇒s≤ : ∀ n m → n <′ m → suc n ≤′ m
<⇒s≤ n m (d , p) = d , (p ; sym (+-suc d n))

s<′s : ∀ n m → suc n <′ suc m → n <′ m
s<′s n m (d , p) = d , (suc-inj p ; +-suc d n)

p<′p : ∀ n m → n <′ m → suc n <′ suc m
p<′p n m (d , p) = d , cong suc (p ; sym (+-suc d n))

p≤′p : ∀ n m → n ≤′ m → suc n ≤′ suc m
p≤′p n m (d , p) = d , (cong suc p ; sym (+-suc d n) )

<′s : ∀ n m → n <′ m → n <′ suc m
<′s n m (d , p) = suc d , cong suc p

≤′s : ∀ n m → n ≤′ m → n ≤′ suc m
≤′s n m (d , p) = suc d , cong suc p

<′⇒≤′ : ∀ n m → n <′ m → n ≤′ m
<′⇒≤′ n m (d , p) = suc d , p

<⇒<′ : ∀ n m → n < m → n <′ m
<⇒<′ zero    (suc m) p = m , cong suc (sym (+-idʳ m))
<⇒<′ (suc n) (suc m) p = p<′p n m (<⇒<′ n m p)

infixl 6 _∔_
_∔_ : ℕ → ℕ → ℕ
zero ∔ y = y
suc x ∔ y = x ∔ suc y

∔≡+ : ∀ x y → x ∔ y ≡ x + y
∔≡+ zero    y = refl
∔≡+ (suc x) y = ∔≡+ x (suc y) ; +-suc x y

-- mod-helper : (k m n j : Nat) → Nat
-- mod-helper k m  zero    j      = k
-- mod-helper k m (suc n)  zero   = mod-helper 0       m n m
-- mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j

open Eqℕ

NonZero : ℕ → Type
NonZero n = T (neg (n ≡ᴮ 0))

x≤x+y : ∀ x y → x ≤ x + y
x≤x+y zero y = tt
x≤x+y (suc x) y = x≤x+y x y

x≤x∔y : ∀ x y → x ≤ x ∔ y
x≤x∔y x y = subst (x ≤_) (sym (∔≡+ x y)) (x≤x+y x y)

infix 4 _≤?_ _<?_
_≤?_ : ∀ n m → Dec (n ≤ m) 
n ≤? m = T? (n ≤ᴮ m)

_<?_ : ∀ n m → Dec (n < m) 
n <? m = T? (n <ᴮ m)

≰⇒> : ∀ n m → ¬ (n ≤ m) → m < n
≰⇒> zero _ n≰m = n≰m tt
≰⇒> (suc n) zero n≰m = tt
≰⇒> (suc n) (suc m) n≰m = ≰⇒> n m n≰m

≮⇒≥ : ∀ n m → ¬ (n < m) → m ≤ n
≮⇒≥ n zero n≮m = tt
≮⇒≥ zero (suc n) n≮m = n≮m tt
≮⇒≥ (suc n₁) (suc n) n≮m = ≮⇒≥ n₁ n n≮m

≤′-trans : ∀ x y z → x ≤′ y → y ≤′ z → x ≤′ z
≤′-trans x y z (k₁ , x≤y) (k₂ , y≤z) .fst = k₁ + k₂
≤′-trans x y z (k₁ , x≤y) (k₂ , y≤z) .snd = y≤z ; cong (k₂ +_) x≤y ; sym (+-assoc k₂ k₁ x) ; cong (_+ x) (+-comm k₂ k₁)

open import Agda.Builtin.Nat

infixl 7 _mod_
_mod_ : (n m : ℕ) → ⦃ _ : NonZero m ⦄ → ℕ
n mod suc m = mod-helper 0 m n m

infixl 7 _div_
_div_ : (n m : ℕ) → ⦃ _ : NonZero m ⦄ → ℕ
n div suc m = div-helper 0 m n m

_∣_ : (n m : ℕ) → ⦃ _ : NonZero n ⦄ → Bool
n ∣ m = (m mod n) ≡ᴮ 0
