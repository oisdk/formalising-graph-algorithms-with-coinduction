{-# OPTIONS --safe #-}

open import Prelude

module Data.Set.Discrete {a} {A : Type a} (disc : Discrete A) where

private
  infix 4 _≟_
  _≟_ : Discrete A
  _≟_ = disc

open import Data.Set
open import Truth
-- open import Data.List.Properties using () renaming (_∈_ to _∈L_; _∉_ to _∉L_; there to thereL)
open import HITs.PropositionalTruncation

∈?-alg : ∀ x → Ψ[ xs ⦂ 𝒦 A ] ↦ Dec (x ∈ xs)
∈?-alg x .snd = prop-coh λ xs → isPropDec (IsProp (⟦ ∈-alg x ⟧ xs))
∈?-alg x .fst ∅ = no λ ()
∈?-alg x .fst (y ∷ xs ⟨ x∈?xs ⟩) =
  map-dec
    (∣_∣ ∘ mapˡ ∣_∣)
    (λ ¬e⊎x∈xs → ∥rec∥ isProp⊥ (∥rec∥ isProp⊥ (¬e⊎x∈xs ∘ inl) ▿ ¬e⊎x∈xs ∘ inr))
    ((x ≟ y) or x∈?xs)

opaque
  _∈?_ : ∀ (x : A) xs → Dec (x ∈ xs)
  x ∈? xs = ⟦ ∈?-alg x ⟧ xs

infixl 6 _\\_
_\\_ : 𝒦 A → A → 𝒦 A
xs \\ x = filter-𝒦 (λ y → neg (does (x ≟ y))) xs

\\-com : ∀ x y xs → xs \\ x \\ y ≡ xs \\ y \\ x
\\-com x y = ⟦ alg x y ⟧
  where
  alg : ∀ x y → Ψ[ xs ⦂ 𝒦 A ] ↦ xs \\ x \\ y ≡ xs \\ y \\ x
  alg x y .snd = eq-coh
  alg x y .fst ∅ = refl
  alg x y .fst (z ∷ xs ⟨ P⟨xs⟩ ⟩) with x ≟ z | y ≟ z
  ... | no  x≢z | no  y≢z = cong (bool′ _ _ ∘ neg) (it-doesn't (y ≟ z) y≢z) ; cong (z ∷_) P⟨xs⟩ ; sym (cong (bool′ _ _ ∘ neg) (it-doesn't (x ≟ z) x≢z))
  ... | no  x≢z | yes y≡z = cong (bool′ _ _ ∘ neg) (it-does (y ≟ z) y≡z) ; P⟨xs⟩
  ... | yes x≡z | no  y≢z = P⟨xs⟩ ; sym (cong (bool′ _ _ ∘ neg) (it-does (x ≟ z) x≡z))
  ... | yes x≡z | yes y≡z = P⟨xs⟩

\\-idem : ∀ x xs → xs \\ x \\ x ≡ xs \\ x
\\-idem x = ⟦ alg x ⟧
  where
  alg : ∀ x → Ψ[ xs ⦂ 𝒦 A ] ↦ xs \\ x \\ x ≡ xs \\ x
  alg x .snd = eq-coh
  alg x .fst ∅ = refl
  alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) with x ≟ y
  ... | no  x≢y = cong (bool′ _ _ ∘ neg) (it-doesn't (x ≟ y) x≢y) ; cong (y ∷_) P⟨xs⟩
  ... | yes x≡y = P⟨xs⟩

open import Data.Empty.Properties

∉rem : ∀ x xs → x ∉ xs \\ x
∉rem x = ⟦ ∉rem-alg x ⟧
  where
  ∉rem-alg : (x : A) → Ψ[ xs ⦂ 𝒦 A ] ↦ x ∉ xs \\ x
  ∉rem-alg x .snd = prop-coh λ _ → isProp¬
  ∉rem-alg x .fst ∅ ()
  ∉rem-alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) with x ≟ y
  ... | no  x≢y = ∥rec∥ isProp⊥ (∥rec∥ isProp⊥ x≢y ▿ P⟨xs⟩)
  ... | yes x≡y = P⟨xs⟩

rem-∉ : ∀ x xs → x ∉ xs → xs \\ x ≡ xs
rem-∉ x = ⟦ rem-∉-alg x ⟧
  where
  rem-∉-alg : ∀ x → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∉ xs → xs \\ x ≡ xs)
  rem-∉-alg x .snd = prop-coh λ _ → isProp→ (trunc _ _)
  rem-∉-alg x .fst ∅ _ = refl
  rem-∉-alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) p with x ≟ y
  ... | yes x≡y = absurd (p ∣ inl ∣ x≡y ∣ ∣)
  ... | no  x≢y = cong (y ∷_) (P⟨xs⟩ (p ∘ ∣_∣ ∘ inr))

rem-∈ : ∀ x y xs → x ∈ xs \\ y → x ∈ xs
rem-∈  x y = ⟦ rem-∈-alg x y ⟧
  where
  rem-∈-alg : ∀ x y → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ xs \\ y → x ∈ xs)
  rem-∈-alg x y .snd = prop-coh λ xs → isProp→ (IsProp (⟦ ∈-alg x ⟧ xs))
  rem-∈-alg x y .fst ∅ ()
  rem-∈-alg x y .fst (z ∷ xs ⟨ P⟨xs⟩ ⟩) with y ≟ z
  ... | yes y≡z = λ p → ∣ inr (P⟨xs⟩ p) ∣
  ... | no  y≢z = ∥rec∥ squash (∣_∣ ∘ mapʳ P⟨xs⟩)

≢-rem : ∀ x y → x ≢ y → ∀ xs → x ∈ xs → x ∈ xs \\ y
≢-rem x y x≢y = ⟦ ≢-rem-alg x y x≢y ⟧
  where
  ≢-rem-alg : ∀ x y → x ≢ y → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ xs → x ∈ xs \\ y)
  ≢-rem-alg x y x≢y .snd = prop-coh λ xs → isProp→ (IsProp (⟦ ∈-alg x ⟧ (xs \\ y)))
  ≢-rem-alg x y x≢y .fst ∅ ()
  ≢-rem-alg x y x≢y .fst (z ∷ xs ⟨ P⟨xs⟩ ⟩) with y ≟ z
  ... | yes y≡z = ∥rec∥ (isProp-∈ x (xs \\ y)) (absurd ∘ ∥rec∥ isProp⊥ (λ x≡z → x≢y (x≡z ; sym y≡z)) ▿ P⟨xs⟩)
  ... | no  y≢z = ∥rec∥ squash (∣_∣ ∘ mapʳ P⟨xs⟩)

-- rem-tail : ∀ x xs → x ∈ xs → xs ≡ x ∷ xs \\ x
-- rem-tail x = ⟦ rem-tail-alg x ⟧
--   where
--   rem-tail-alg : ∀ x → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ xs → xs ≡ x ∷ xs \\ x)
--   rem-tail-alg x .snd = prop-coh λ _ → isProp→ (trunc _ _)
--   rem-tail-alg x .fst ∅ ()
--   rem-tail-alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) with x ≟ y
--   ... | no  x≢y = ∥rec∥ (trunc _ _) (∥rec∥ (trunc _ _) (absurd ∘ x≢y) ▿ (λ x∈xs → cong (y ∷_) (P⟨xs⟩ x∈xs) ; comm y x _))
--   ... | yes x≡y with x ∈? xs
--   ... | no  x∉xs = λ p → sym (cong₂ _∷_ x≡y (rem-∉ x xs x∉xs))
--   ... | yes x∈xs = λ _ → cong₂ _∷_ (sym x≡y) (P⟨xs⟩ x∈xs) ; dup x _

-- rem-cons : ∀ (x : A) (xs : 𝒦 A) → x ∷ xs ≡ x ∷ xs \\ x
-- rem-cons x xs = rem-tail x (x ∷ xs) ∣ inl ∣ refl ∣ ∣ ; cong (x ∷_) (cong (bool′ _ _ ∘ neg) (it-does (x ≟ x) refl))

-- ∈-eq-lemma : ∀ x xs ys → x ∉ xs → (∀ z → z ∈ x ∷ xs ⟷ z ∈ ys) → ∀ z → z ∈ xs ⟷ z ∈ ys \\ x
-- ∈-eq-lemma x xs ys x∉xs xxs↭ys z .fst z∈xs with z ≟ x
-- ... | yes z≡x = absurd (x∉xs (subst (_∈ xs) z≡x z∈xs) )
-- ... | no  z≢x =
--   ≢-rem z x z≢x ys (xxs↭ys z .fst ∣ inr z∈xs ∣)
-- ∈-eq-lemma x xs ys x∉xs xxs↭ys z .snd z∈rys with z ≟ x
-- ... | yes z≡x = absurd (∉rem x ys (subst (_∈ ys \\ x) z≡x z∈rys))
-- ... | no z≢x =
--   ∥rec∥
--     (IsProp (⟦ ∈-alg z ⟧ xs))
--     (absurd ∘ ∥rec∥ isProp⊥ z≢x ▿ id)
--     (xxs↭ys z .snd (rem-∈ z x ys z∈rys))

-- ⊆-antisym : (xs ys : 𝒦 A) → xs ⊆ ys → ys ⊆ xs → xs ≡ ys
-- ⊆-antisym = ⟦ ⊆-antisym-alg ⟧
--   where
--   ⊆-antisym-alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (∀ ys → xs ⊆ ys → ys ⊆ xs → xs ≡ ys)
--   ⊆-antisym-alg .snd = prop-coh λ _ → isPropΠ λ _ → isProp→ (isProp→ (trunc _ _))
--   ⊆-antisym-alg .fst ∅ ys xs⊆ys ys⊆xs = sym (∀∉ ys λ y y∈ys → ∉∅ y (ys⊆xs y y∈ys))
--   ⊆-antisym-alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) ys xs⊆ys ys⊆xs with x ∈? xs
--   ... | yes x∈xs =
--    let h = ∈-cons x xs x∈xs
--    in sym h ; P⟨xs⟩ ys (λ z z∈xs → xs⊆ys z ∣ inr z∈xs ∣) (λ z z∈ys → subst (z ∈_) (sym h) (ys⊆xs z z∈ys))
--   ... | no  x∉xs =
--     let h = ∈-eq-lemma x xs ys x∉xs (λ z → xs⊆ys z , ys⊆xs z) ⦂ (∀ z → z ∈ xs ⟷ z ∈ ys \\ x)
--     in cong (x ∷_) (P⟨xs⟩ (ys \\ x) (fst ∘′ h) (snd ∘′ h)) ; sym (rem-tail x ys (xs⊆ys x ∣ inl ∣ refl ∣ ∣))

-- fromList-eq : (xs ys : List A) → (∀ x → x ∈L xs ⟷ x ∈L ys) → 𝒦-fromList xs ≡ 𝒦-fromList ys
-- fromList-eq xs ys p =
--   ⊆-antisym
--     (𝒦-fromList xs)
--     (𝒦-fromList ys)
--     (λ x → ∥rec∥ (isProp-∈ x (𝒦-fromList ys)) (∈-fromList x ys ∘ p x .fst) ∘ fromList-∈ x xs)
--     (λ x → ∥rec∥ (isProp-∈ x (𝒦-fromList xs)) (∈-fromList x xs ∘ p x .snd) ∘ fromList-∈ x ys)

-- infixr 5 _∩_
-- _∩_ : 𝒦 A → 𝒦 A → 𝒦 A
-- xs ∩ ys = filter-𝒦 (λ x → does (x ∈? ys)) xs

-- ∈-∩ : ∀ x xs ys → x ∈ xs ∩ ys ⟷ (x ∈ xs × x ∈ ys)
-- ∈-∩ x xs ys = ⟦ ∈-∩-alg x ys ⟧ xs
--   where
--   ∈-∩-alg : ∀ x ys → Ψ[ xs ⦂ 𝒦 A ] ↦ x ∈ xs ∩ ys ⟷ ((x ∈ xs) × (x ∈ ys))
--   ∈-∩-alg x ys .snd = prop-coh λ xs → isProp× (isProp→ (isProp× (isProp-∈ x xs) (isProp-∈ x ys))) (isProp→ (isProp-∈ x (xs ∩ ys)))
--   ∈-∩-alg x ys .fst ∅ .fst ()
--   ∈-∩-alg x ys .fst ∅ .snd = fst
--   ∈-∩-alg x ys .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) .fst x∈yx∩ys with y ∈? ys
--   ... | no y∉ys = map₁ (∣_∣ ∘ inr) (P⟨xs⟩ .fst x∈yx∩ys)
--   ... | yes y∈ys =
--     ∥rec∥
--       (isProp× squash (isProp-∈ x ys))
--       ((λ x≡y → ∣ inl x≡y ∣ , subst (_∈ ys) (∥rec∥ (Discrete→isSet _≟_ _ _) sym x≡y) y∈ys) ▿ map₁ (∣_∣ ∘ inr) ∘ P⟨xs⟩ .fst) x∈yx∩ys
--   ∈-∩-alg x ys .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) .snd (x∈xs , x∈ys) with y ∈? ys
--   ... | no y∉ys = P⟨xs⟩ .snd (∥rec∥ (isProp-∈ x xs) (absurd ∘ ∥rec∥ isProp⊥ (λ x≡y → y∉ys (subst (_∈ ys) x≡y x∈ys)) ▿ id) x∈xs , x∈ys)
--   ... | yes y∈ys = ∥map∥ (mapʳ (P⟨xs⟩ .snd ∘ (_, x∈ys))) x∈xs

-- _⊆?_ : ∀ xs ys → Dec (xs ⊆ ys)
-- xs ⊆? ys = case All-𝒦? {P = λ x → ⟦ ∈-alg x ⟧ ys} (λ x → x ∈? ys) xs of
--   λ { (no ¬xs⊆) → no λ xs⊆ys → ¬xs⊆ (∈-All-𝒦 _ xs xs⊆ys)
--     ; (yes xs⊆) → yes λ x x∈xs → All-𝒦-∈ _ x xs xs⊆ x∈xs
--     }

-- discreteSet : Discrete (𝒦 A)
-- discreteSet xs ys =
--   map-dec
--     (uncurry (⊆-antisym xs ys))
--     (λ ¬p xs≡ys → ¬p ((λ x → subst (x ∈_) xs≡ys) , (λ x → subst (x ∈_) (sym xs≡ys))))
--     (case (xs ⊆? ys , ys ⊆? xs) of
--     λ { (no xs⊈ys , _) → no (xs⊈ys ∘ fst)
--       ; (_ , no ys⊈xs) → no (ys⊈xs ∘ snd)
--       ; (yes xs⊆ys , yes ys⊆xs) → yes (xs⊆ys , ys⊆xs)
--     })

-- import Data.List.Properties.Discrete disc as L

-- \\-hom : ∀ (x : A) xs → 𝒦-fromList xs \\ x ≡ 𝒦-fromList (xs L.\\ x)
-- \\-hom x [] = refl
-- \\-hom x (y ∷ xs) with x ≟ y
-- ... | yes x≡y = \\-hom x xs
-- ... | no  x≢y = cong (y ∷_) (\\-hom x xs)

-- fromList-nub : (xs : List A) → 𝒦-fromList xs ≡ 𝒦-fromList (L.nub xs)
-- fromList-nub [] = refl
-- fromList-nub (x ∷ xs) =
--   𝒦-fromList (x ∷ xs) ≡⟨⟩
--   x ∷ 𝒦-fromList xs ≡⟨ cong (x ∷_) (fromList-nub xs) ⟩
--   x ∷ 𝒦-fromList (L.nub xs) ≡⟨ rem-tail x (x ∷ 𝒦-fromList (L.nub xs)) ∣ inl ∣ refl ∣ ∣ ⟩
--   x ∷ (x ∷ 𝒦-fromList (L.nub xs)) \\ x ≡⟨ cong (x ∷_) (cong (bool′ _ _ ∘ neg) (it-does (x ≟ x) refl)) ⟩
--   x ∷ 𝒦-fromList (L.nub xs) \\ x ≡⟨ cong (x ∷_) (\\-hom x (L.nub xs)) ⟩
--   x ∷ 𝒦-fromList (L.nub xs L.\\ x) ≡⟨⟩
--   𝒦-fromList (x ∷ L.nub xs L.\\ x) ≡⟨⟩
--   𝒦-fromList (L.nub (x ∷ xs)) ∎
