{-# OPTIONS --safe #-}
module Data.Set where

open import Prelude

infixr 5 _∷_
data 𝒦 (A : Type a) : Type a where
  _∷_ : A → 𝒦 A → 𝒦 A
  ∅ : 𝒦 A
  dup : ∀ x xs → x ∷ x ∷ xs ≡ x ∷ xs
  comm : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isSet (𝒦 A)

private variable 
  -- p : Level
  -- P : A → Type p
  x y z : A
  xs ys zs : 𝒦 A

infixr 5 _∷_⟨_⟩
data 𝔎 {p} (A : Type a) (P : 𝒦 A → Type p) : Type (a ℓ⊔ p) where
  ∅ : 𝔎 A P
  _∷_⟨_⟩ : A → (xs : 𝒦 A) → (P⟨xs⟩ : P xs) → 𝔎 A P

embed : 𝔎 A P → 𝒦 A
embed ∅ = ∅
embed (x ∷ xs ⟨ P⟨xs⟩ ⟩) = x ∷ xs

Alg : (P : 𝒦 A → Type p) → Type _
Alg P = (xs : 𝔎 _ P) → P (embed xs)

record Coherent {A : Type a} {P : 𝒦 A → Type p} (ϕ : Alg P) : Type (a ℓ⊔ p) where
  no-eta-equality
  field
    c-trunc : ∀ xs → isSet (P xs)

    c-com : ∀ x y xs P⟨xs⟩ →
            PathP
              (λ i → P (comm x y xs i))
              (ϕ (x ∷ (y ∷ xs) ⟨ ϕ (y ∷ xs ⟨ P⟨xs⟩ ⟩) ⟩))
              (ϕ (y ∷ (x ∷ xs) ⟨ ϕ (x ∷ xs ⟨ P⟨xs⟩ ⟩) ⟩ ))

    c-dup : ∀ x xs P⟨xs⟩ →
            PathP
              (λ i → P (dup x xs i))
              (ϕ (x ∷ (x ∷ xs) ⟨ ϕ (x ∷ xs ⟨ P⟨xs⟩ ⟩) ⟩))
              (ϕ (x ∷ xs ⟨ P⟨xs⟩ ⟩))
open Coherent public

𝒦-foldr : (A → B → B) → B → Alg (const B)
𝒦-foldr f b ∅ = b
𝒦-foldr f b (x ∷ xs ⟨ P⟨xs⟩ ⟩) = f x P⟨xs⟩

Ψ : (𝒦 A → Type p) → Type _
Ψ P = Σ[ ϕ ⦂ Alg P ] × Coherent ϕ

infixr -1 Ψ-syntax
Ψ-syntax : (A : Type a) → (𝒦 A → Type p) → Type _
Ψ-syntax _ = Ψ

syntax Ψ-syntax A (λ x → e) = Ψ[ x ⦂ 𝒦 A ] ↦ e

ψ : Type a → Type b → Type _
ψ A B = Ψ {A = A} (const B)

⟦_⟧ : {P : 𝒦 A → Type p} → Ψ P → (xs : 𝒦 A) → P xs
⟦ alg ⟧ ∅ = alg .fst ∅
⟦ alg ⟧ (x ∷ xs) = alg .fst (x ∷ xs ⟨ ⟦ alg ⟧ xs ⟩)
⟦ alg ⟧ (comm x y xs i) = alg .snd .c-com x y xs (⟦ alg ⟧ xs) i
⟦ alg ⟧ (dup x xs i) = alg .snd .c-dup x xs (⟦ alg ⟧ xs) i
⟦ alg ⟧ (trunc xs ys p q i j) =
  isOfHLevel→isOfHLevelDep 2
    (alg .snd .c-trunc)
    (⟦ alg ⟧ xs) (⟦ alg ⟧ ys)
    (cong ⟦ alg ⟧ p) (cong ⟦ alg ⟧ q)
    (trunc xs ys p q)
    i j

opaque
  prop-coh : {A : Type a} {P : 𝒦 A → Type p} {alg : Alg P} → (∀ xs → isProp (P xs)) → Coherent alg
  prop-coh P-isProp .c-trunc xs = isProp→isSet (P-isProp xs)
  prop-coh {P = P} {alg = alg} P-isProp .c-dup x xs ψ⟨xs⟩ =
    toPathP (P-isProp (x ∷ xs) (transp (λ i → P (dup x xs i)) i0 (alg (x ∷ (x ∷ xs) ⟨ alg (x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩))) (alg (x ∷ xs ⟨ ψ⟨xs⟩ ⟩)))
  prop-coh {P = P} {alg = alg} P-isProp .c-com x y xs ψ⟨xs⟩ =
    toPathP (P-isProp (y ∷ x ∷ xs) (transp (λ i → P (comm x y xs i)) i0 (alg (x ∷ (y ∷ xs) ⟨ alg (y ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩))) (alg (y ∷ (x ∷ xs) ⟨ alg (x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩)))

infix 4 _⊜_
record AnEquality (A : Type a) : Type a where
  constructor _⊜_
  field lhs rhs : 𝒦 A
open AnEquality

EqualityProof-Alg : {B : Type b} (A : Type a) (P : 𝒦 A → AnEquality B) → Type (a ℓ⊔ b)
EqualityProof-Alg A P = Alg (λ xs → let Pxs = P xs in lhs Pxs ≡ rhs Pxs)

opaque
  eq-coh : {A : Type a} {B : Type b} {P : 𝒦 A → AnEquality B} {alg : EqualityProof-Alg A P} → Coherent alg
  eq-coh {P = P} = prop-coh λ xs → let Pxs = P xs in trunc (lhs Pxs) (rhs Pxs)

union-alg : ψ A (𝒦 A → 𝒦 A)
union-alg .fst ∅                  ys = ys
union-alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩)  ys = x ∷ P⟨xs⟩ ys
union-alg .snd .c-trunc _ = isSetΠ λ _ → trunc
union-alg .snd .c-com x y xs P⟨xs⟩ i ys = comm x y (P⟨xs⟩ ys) i
union-alg .snd .c-dup x xs P⟨xs⟩ i ys = dup x (P⟨xs⟩ ys) i

infixr 5 _∪_
_∪_ : 𝒦 A → 𝒦 A → 𝒦 A
_∪_ = ⟦ union-alg ⟧

∷-distrib : ∀ (x : A) xs ys → x ∷ (xs ∪ ys) ≡ xs ∪ (x ∷ ys)
∷-distrib x = ⟦ alg x ⟧
  where
  alg : ∀ x → Ψ[ xs ⦂ 𝒦 A ] ↦ (∀ ys → x ∷ (xs ∪ ys) ≡ xs ∪ (x ∷ ys))
  alg x .fst ∅ ys = refl
  alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) ys = comm x y (xs ∪ ys) ; cong (y ∷_) (P⟨xs⟩ ys)
  alg x .snd = prop-coh λ _ → isPropΠ λ _ → trunc _ _ 

open import Path.Reasoning

∪-idem : (xs : 𝒦 A) → xs ∪ xs ≡ xs
∪-idem = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ ((xs ∪ xs) ≡ xs)
  alg .fst ∅ = refl
  alg .snd = eq-coh
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) =
    (x ∷ xs) ∪ (x ∷ xs) ≡˘⟨ ∷-distrib x (x ∷ xs) xs ⟩
    x ∷ x ∷ xs ∪ xs ≡⟨ dup x (xs ∪ xs) ⟩
    x ∷ xs ∪ xs ≡⟨ cong (x ∷_) P⟨xs⟩ ⟩
    x ∷ xs ∎

∪-idʳ : (xs : 𝒦 A) → (xs ∪ ∅ ≡ xs)
∪-idʳ = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (xs ∪ ∅ ≡ xs)
  alg .fst ∅ = refl
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (x ∷_) P⟨xs⟩
  alg .snd = eq-coh

∪-com : (xs ys : 𝒦 A) → (xs ∪ ys ≡ ys ∪ xs)
∪-com = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (∀ ys → xs ∪ ys ≡ ys ∪ xs)
  alg .fst ∅ ys = sym (∪-idʳ ys)
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) ys = cong (x ∷_) (P⟨xs⟩ ys) ; ∷-distrib x ys xs
  alg .snd = prop-coh λ _ → isPropΠ λ _ → trunc _ _

∪-assoc : (xs ys zs : 𝒦 A) → ((xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs))
∪-assoc = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (∀ ys zs → (xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs))
  alg .fst ∅ ys zs = refl
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) ys zs = cong (x ∷_) (P⟨xs⟩ ys zs)
  alg .snd = prop-coh λ _ → isPropΠ λ _ → isPropΠ λ _ → trunc _ _

𝒦-map : (A → B) → 𝒦 A → 𝒦 B
𝒦-map f = ⟦ map-alg f ⟧
  where
  map-alg : (A → B) → Ψ[ xs ⦂ 𝒦 A ] ↦ 𝒦 B
  map-alg f .fst ∅ = ∅
  map-alg f .fst (x ∷ _ ⟨ xs ⟩) = f x ∷ xs
  map-alg f .snd .c-trunc _ = trunc
  map-alg f .snd .c-com x y _ = comm (f x) (f y)
  map-alg f .snd .c-dup x _ = dup (f x)

map-∪ : (f : A → B) (xs ys : 𝒦 A) → 𝒦-map f xs ∪ 𝒦-map f ys ≡ 𝒦-map f (xs ∪ ys)
map-∪ f xs ys = ⟦ alg f ys ⟧ xs
  where
  alg : (f : A → B) (ys : 𝒦 A) → Ψ[ xs ⦂ 𝒦 A ] ↦ ((𝒦-map f xs ∪ 𝒦-map f ys) ≡ 𝒦-map f (xs ∪ ys))
  alg f ys .fst ∅ = refl
  alg f ys .fst (x ∷ _ ⟨ xs ⟩) = cong (f x ∷_) xs
  alg f ys .snd = prop-coh λ _ → trunc _ _

map-id : (xs : 𝒦 A) → 𝒦-map id xs ≡ xs
map-id = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (𝒦-map id xs ≡ xs)
  alg .fst ∅ = refl
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (x ∷_) P⟨xs⟩
  alg .snd = prop-coh λ _ → trunc _ _

𝒦-map-comp : (g : B → C) (f : A → B) (xs : 𝒦 A) → 𝒦-map g (𝒦-map f xs) ≡ 𝒦-map (g ∘ f) xs
𝒦-map-comp g f = ⟦ alg g f ⟧
  where
  alg : (g : B → C) (f : A → B) → Ψ[ xs ⦂ 𝒦 A ] ↦ 𝒦-map g (𝒦-map f xs) ≡ 𝒦-map (g ∘ f) xs
  alg g f .snd = eq-coh
  alg g f .fst ∅ = refl
  alg g f .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (g (f x) ∷_) P⟨xs⟩

null : 𝒦 A → Bool
null = ⟦ null-alg ⟧
  where
  null-alg : Ψ[ xs ⦂ 𝒦 A ] ↦ Bool
  null-alg .fst ∅ = true
  null-alg .fst (_ ∷ _ ⟨ _ ⟩) = false
  null-alg .snd .c-trunc _ = isSetBool
  null-alg .snd .c-com x y xs P⟨xs⟩ = refl
  null-alg .snd .c-dup x xs P⟨xs⟩ = refl

𝒦-cat-maybes : (A → Maybe B) → 𝒦 A → 𝒦 B
𝒦-cat-maybes {A = A} {B = B} p = ⟦ alg p ⟧
  where
  alg : (A → Maybe B) → Ψ[ xs ⦂ 𝒦 A ] ↦ 𝒦 B
  alg p .fst ∅ = ∅
  alg p .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = maybe id _∷_ (p x) P⟨xs⟩
  alg p .snd .c-trunc _ = trunc
  alg p .snd .c-com x y xs P⟨xs⟩ with p x | p y
  ... | just x | just y = comm x y P⟨xs⟩
  ... | just x | nothing = refl
  ... | nothing | _ = refl
  alg p .snd .c-dup x xs P⟨xs⟩ with p x
  ... | just x = dup x P⟨xs⟩
  ... | nothing = refl

module _ {A : Type a} where
  open import Truth
  open import HITs.PropositionalTruncation

  ∈-alg : A → Ψ[ xs ⦂ 𝒦 A ] ↦ Ω a
  ∈-alg x .fst ∅ = False
  ∈-alg x .fst (y ∷ _ ⟨ P⟨xs⟩ ⟩) = (x |≡| y) |∨| P⟨xs⟩
  ∈-alg x .snd .c-trunc _ = isSetΩ
  ∈-alg x .snd .c-com y z xs x∈xs =
    (x |≡| y) |∨| ((x |≡| z) |∨| x∈xs) ≡˘⟨ ∨-assoc (x |≡| y) _ _ ⟩
    ((x |≡| y) |∨| (x |≡| z)) |∨| x∈xs ≡⟨ cong (_|∨| x∈xs) (∨-com _ _) ⟩
    ((x |≡| z) |∨| (x |≡| y)) |∨| x∈xs ≡⟨ ∨-assoc (x |≡| z) _ _ ⟩
    (x |≡| z) |∨| ((x |≡| y) |∨| x∈xs) ∎
  ∈-alg x .snd .c-dup y xs x∈xs =
    (x |≡| y) |∨| ((x |≡| y) |∨| x∈xs) ≡˘⟨ ∨-assoc (x |≡| y) _ _ ⟩
    ((x |≡| y) |∨| (x |≡| y)) |∨| x∈xs ≡⟨ cong (_|∨| x∈xs) (∨-idem (x |≡| y) ) ⟩
    (x |≡| y) |∨| x∈xs ∎

  infixr 5 _∈_ _∉_
  _∈_ : A → 𝒦 A → Type a
  x ∈ xs = ProofOf (⟦ ∈-alg x ⟧ xs)


  isProp-∈ : ∀ x xs → isProp (x ∈ xs)
  isProp-∈ x xs = IsProp (⟦ ∈-alg x ⟧ xs)

  _∉_ : A → 𝒦 A → Type a
  x ∉ xs = ¬ (x ∈ xs)

  ∀∉ : ∀ xs → (∀ x → x ∉ xs) → xs ≡ ∅
  ∀∉ = ⟦ ∀∉-alg ⟧
    where
    ∀∉-alg : Ψ[ xs ⦂ 𝒦 A ] ↦ ((∀ x → x ∉ xs) → xs ≡ ∅)
    ∀∉-alg .snd = prop-coh λ _ → isProp→ (trunc _ _)
    ∀∉-alg .fst ∅ x = refl
    ∀∉-alg .fst (y ∷ _ ⟨ _ ⟩) x∉xs = absurd (x∉xs y ∣ inl ∣ refl ∣ ∣)

  ∉∅ : ∀ x → x ∉ ∅
  ∉∅ x ()

  ∈-cons : ∀ x xs → x ∈ xs → xs ≡ x ∷ xs
  ∈-cons x = ⟦ ∈-cons-alg x ⟧
    where
    ∈-cons-alg : ∀ x → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ xs → xs ≡ x ∷ xs)
    ∈-cons-alg x .snd = prop-coh λ _ → isProp→ (trunc _ _)
    ∈-cons-alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) =
      ∥elim∥
        (λ _ → trunc _ _)
        λ { (inl ∣x≡y∣) → ∥rec∥ (trunc _ _) (λ x≡y → sym (dup y xs) ; cong (_∷ y ∷ xs) (sym x≡y)) ∣x≡y∣
          ; (inr x∈xs) → cong (y ∷_) (P⟨xs⟩ x∈xs) ; comm y x xs
          }

  Disjoint : 𝒦 A → 𝒦 A → Type a
  Disjoint xs ys = ∀ x → x ∈ xs → x ∉ ys

  infix 4 _⊆_
  _⊆_ : 𝒦 A → 𝒦 A → Type _
  xs ⊆ ys = ∀ x → x ∈ xs → x ∈ ys


  disj-com : ∀ xs ys → Disjoint xs ys → Disjoint ys xs
  disj-com xs ys p x x∈xs x∈ys = p x x∈ys x∈xs

  module _ (p : A → Bool) where
    partition-𝒦 : 𝒦 A → 𝒦 A × 𝒦 A
    partition-𝒦 = ⟦ partition-alg ⟧
      where
      partition-alg : Ψ[ xs ⦂ 𝒦 A ] ↦ 𝒦 A × 𝒦 A
      partition-alg .fst ∅ = ∅ , ∅
      partition-alg .fst (x ∷ _ ⟨ fls , trs ⟩) = let px = p x in ((if px then fls else x ∷ fls) , (if px then x ∷ trs else trs))
      partition-alg .snd .c-trunc _ = isSet× trunc trunc
      partition-alg .snd .c-com x y _ (fls , trs) with p x | p y 
      ... | false | false = cong (_, trs) (comm x y fls)
      ... | false | true = refl
      ... | true | false = refl
      ... | true | true = cong (fls ,_) (comm x y trs)
      partition-alg .snd .c-dup x _ (fls , trs) with p x
      ... | false = cong (_, trs) (dup x fls)
      ... | true = cong (fls ,_) (dup x trs)

    partition-𝒦-∪ : (xs : 𝒦 A) → uncurry _∪_ (partition-𝒦 xs) ≡ xs
    partition-𝒦-∪ = ⟦ alg ⟧
      where
      alg : Ψ[ xs ⦂ 𝒦 A ] ↦ uncurry _∪_ (partition-𝒦 xs) ≡ xs
      alg .snd = eq-coh
      alg .fst ∅ = refl
      alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) with p x
      ... | false = cong (x ∷_) P⟨xs⟩
      ... | true  = sym (uncurry (∷-distrib x) (partition-𝒦 xs)) ; cong (x ∷_) P⟨xs⟩

    filter-𝒦 : 𝒦 A → 𝒦 A
    filter-𝒦 = snd ∘ partition-𝒦

    filter-idem : ∀ xs → filter-𝒦 (filter-𝒦 xs) ≡ filter-𝒦 xs
    filter-idem = ⟦ alg ⟧
      where
      alg : Ψ[ xs ⦂ 𝒦 A ] ↦ filter-𝒦 (filter-𝒦 xs) ≡ filter-𝒦 xs
      alg .fst ∅ = refl
      alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) with p x | inspect p x
      ... | false | _ = P⟨xs⟩
      ... | true | 〖 eq 〗 = cong (bool′ _ _) eq ; cong (x ∷_) P⟨xs⟩
      alg .snd = eq-coh

    T→∈-filter : ∀ xs x → T (p x) → x ∈ xs → x ∈ filter-𝒦 xs
    T→∈-filter xs x Tpx = ⟦ alg x Tpx ⟧ xs
      where
      alg : ∀ x → T (p x) → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ xs → x ∈ filter-𝒦 xs)
      alg x Tpx .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) x∈xs with p y | inspect p y
      ... | true  | 〖 eq 〗 = ∥map∥ (mapʳ P⟨xs⟩) x∈xs
      ... | false | 〖 eq 〗 = P⟨xs⟩ (∥rec∥ (isProp-∈ x xs) (absurd ∘ ∥rec∥ isProp⊥ (λ e → subst T (cong p e ; eq) Tpx) ▿ id) x∈xs)
      alg x Tpx .snd = prop-coh λ xs → isProp→ (isProp-∈ x (filter-𝒦 xs))

    ∈-filter→T : ∀ xs x → x ∈ filter-𝒦 xs → T (p x)
    ∈-filter→T xs x = ⟦ alg x ⟧ xs
      where
      open import Data.Bool.Properties

      alg : ∀ x → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ filter-𝒦 xs → T (p x))
      alg x .snd = prop-coh λ xs → isProp→ (isPropT (p x))
      alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) x∈fpxs with p y | inspect p y
      ... | false | 〖 eq 〗 = P⟨xs⟩ x∈fpxs
      ... | true  | 〖 eq 〗 = ∥rec∥ (isPropT (p x)) (∥rec∥ (isPropT (p x)) (λ x≡y → subst T (sym (cong p x≡y ; eq)) tt) ▿ P⟨xs⟩) x∈fpxs

    filter-⊆ : ∀ xs → filter-𝒦 xs ⊆ xs
    filter-⊆ xs x = ⟦ alg x ⟧ xs
      where
      alg : ∀ x → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ filter-𝒦 xs → x ∈ xs)
      alg x .snd = prop-coh λ xs → isProp→ (isProp-∈ x xs)
      alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) x∈fpxs with p y | inspect p y
      ... | false | 〖 eq 〗 = ∣ inr (P⟨xs⟩ x∈fpxs) ∣
      ... | true  | 〖 eq 〗 = ∥map∥ (mapʳ P⟨xs⟩) x∈fpxs


  𝒦-fromList : List A → 𝒦 A
  𝒦-fromList = foldr _∷_ ∅

  fromListed : List A ↠ 𝒦 A
  fromListed .fst = 𝒦-fromList
  fromListed .snd = ⟦ alg ⟧
    where
    alg : Ψ[ xs ⦂ 𝒦 A ] ↦ ∥ Surjected 𝒦-fromList xs ∥
    alg .snd = prop-coh λ _ → squash
    alg .fst ∅ = ∣ [] ,↠ refl ∣
    alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = ∥map∥ (λ s → (x ∷ s .image) ,↠ cong (x ∷_) (s .reflects)) P⟨xs⟩

  opaque
    there : ∀ {x} y xs → x ∈ xs → x ∈ y ∷ xs
    there _ _ x∈xs = ∣ inr x∈xs ∣

  ∈-∪ˡ : ∀ {x} xs ys → x ∈ xs → x ∈ xs ∪ ys
  ∈-∪ˡ xs ys = ⟦ alg ys ⟧ xs
    where
    alg : ∀ {x } ys → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ xs → x ∈ xs ∪ ys)
    alg ys .snd = prop-coh λ xs → isProp→ (isProp-∈ _ (xs ∪ _))
    alg ys .fst (x ∷ xs ⟨ k ⟩) = ∥map∥ (mapʳ k)

  ∈-∪ʳ : ∀ {x} xs ys → x ∈ ys → x ∈ xs ∪ ys
  ∈-∪ʳ xs ys = ⟦ alg ys ⟧ xs
    where
    alg : ∀ {x} ys → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ ys → x ∈ xs ∪ ys)
    alg ys .snd = prop-coh λ xs → isProp→ (isProp-∈ _ (xs ∪ _))
    alg ys .fst ∅ = id
    alg ys .fst (x ∷ xs ⟨ k ⟩) x∈ys = there x (xs ∪ _) (k x∈ys)

  ∈-⊎ : ∀ x xs ys → x ∈ xs ∪ ys → ∥ x ∈ xs ⊎ x ∈ ys ∥
  ∈-⊎ x xs ys = ⟦ alg x ys ⟧ xs
    where
    alg : ∀ x ys → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ xs ∪ ys → ∥ x ∈ xs ⊎ x ∈ ys ∥)
    alg x ys .snd = prop-coh (λ _ → isProp→ squash)
    alg x ys .fst ∅ x∈xs∪ys = ∣ inr x∈xs∪ys ∣
    alg x ys .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) = ∥rec∥ squash (∣_∣ ∘ inl ∘ ∣_∣ ∘ inl ▿ ∥map∥ (mapˡ (∣_∣ ∘ inr)) ∘ P⟨xs⟩)

  in-head : ∀ {x y : A} {xs} → x ≡ y → x ∈ y ∷ xs
  in-head x≡y = ∣ inl ∣ x≡y ∣ ∣

  open import Data.List.Properties using () renaming (_∈_ to _∈L_; _∉_ to _∉L_; there to thereL)
  open import Data.Fin

  ∈-fromList : ∀ x xs → x ∈L xs → x ∈ 𝒦-fromList xs
  ∈-fromList x (y ∷ xs) (fzero   , x∈xs) = ∣ inl ∣ sym x∈xs ∣ ∣
  ∈-fromList x (y ∷ xs) (fsuc i , x∈xs) = ∣ inr (∈-fromList x xs (i , x∈xs)) ∣

  fromList-∈ : ∀ x xs → x ∈ 𝒦-fromList xs → ∥ x ∈L xs ∥
  fromList-∈ x (y ∷ xs) = ∥rec∥ squash (∥map∥ (λ x≡y → fzero , sym x≡y) ▿ ∥map∥ (thereL y) ∘ fromList-∈ x xs)

  All-𝒦 : ∀ {p} (P : A → Ω p) → 𝒦 A → Ω p
  All-𝒦 P = ⟦ alg P ⟧ where
    alg : (P : A → Ω p) → Ψ[ xs ⦂ 𝒦 A ] ↦ Ω p
    alg P .fst ∅ = True
    alg P .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = P x |∧| P⟨xs⟩
    alg P .snd .c-trunc _ = isSetΩ
    alg P .snd .c-com x y _ P⟨xs⟩ = sym (∧-assoc (P x) (P y) P⟨xs⟩) ; cong (_|∧| P⟨xs⟩) (∧-com (P x) (P y)) ; ∧-assoc (P y) (P x) P⟨xs⟩
    alg P .snd .c-dup x _ P⟨xs⟩ = sym (∧-assoc (P x) (P x) P⟨xs⟩) ; cong (_|∧| P⟨xs⟩) (∧-idem (P x))

  All-𝒦? : ∀ {p} {P : A → Ω p} (P? : ∀ x → Dec (P x .ProofOf)) → ∀ xs → Dec (All-𝒦 P xs .ProofOf)
  All-𝒦? P? = ⟦ alg P? ⟧
    where
    alg : ∀ {p} {P : A → Ω p} (P? : ∀ x → Dec (P x .ProofOf)) → Ψ[  xs ⦂ 𝒦 A ] ↦ Dec (All-𝒦 P xs .ProofOf)
    alg P? .snd = prop-coh λ xs → isPropDec (All-𝒦 _ xs .IsProp)
    alg P? .fst ∅ = yes Poly-tt
    alg P? .fst (x ∷ _ ⟨ P⟨xs⟩ ⟩) with P? x
    alg P? .fst (x ∷ _ ⟨ P⟨xs⟩ ⟩) | no ¬Px = no (¬Px ∘ fst)
    alg P? .fst (x ∷ _ ⟨ no ¬P⟨xs⟩ ⟩) | _ = no (¬P⟨xs⟩ ∘ snd)
    alg P? .fst (x ∷ _ ⟨ yes P⟨xs⟩ ⟩) | yes Px = yes (Px , P⟨xs⟩)

  All-𝒦-∈ : ∀ {p} (P : A → Ω p) → ∀ x xs → ProofOf (All-𝒦 P xs) → x ∈ xs → ProofOf (P x)
  All-𝒦-∈ P x = ⟦ alg P x ⟧
    where
    alg : ∀ {p} (P : A → Ω p) → ∀ x → Ψ[ xs ⦂ 𝒦 A ] ↦ (ProofOf (All-𝒦 P xs) → x ∈ xs → ProofOf (P x))
    alg P x .snd = prop-coh (λ xs → isProp→ (isProp→ (IsProp (P x))))
    alg P x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) (px , apxs) =
      ∥rec∥ (IsProp (P x)) (∥rec∥ (IsProp (P x)) (λ x≡y → subst (ProofOf ∘ P) (sym x≡y) px ) ▿ P⟨xs⟩ apxs)

  ∈-All-𝒦 : ∀ {p} (P : A → Ω p) → ∀ xs → (∀ x → x ∈ xs → P x .ProofOf) → All-𝒦 P xs .ProofOf
  ∈-All-𝒦 P = ⟦ alg P ⟧
    where
    alg : ∀ {p} (P : A → Ω p) → Ψ[ xs ⦂ 𝒦 A ] ↦ ((∀ x → x ∈ xs → P x .ProofOf) → All-𝒦 P xs .ProofOf)
    alg P .snd = prop-coh λ xs → isProp→ (IsProp (All-𝒦 P xs))
    alg P .fst ∅ k = Poly-tt
    alg P .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) k = k x ∣ inl ∣ refl ∣ ∣ , P⟨xs⟩ λ y y∈xs → k y ∣ inr y∈xs ∣

  Any-𝒦 : ∀ {p} (P : A → Ω p) → 𝒦 A → Ω p
  Any-𝒦 P = ⟦ alg P ⟧ where
    alg : (P : A → Ω p) → Ψ[ xs ⦂ 𝒦 A ] ↦ Ω p
    alg P .fst ∅ = False
    alg P .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = P x |∨| P⟨xs⟩
    alg P .snd .c-trunc _ = isSetΩ
    alg P .snd .c-com x y _ P⟨xs⟩ = sym (∨-assoc (P x) (P y) P⟨xs⟩) ; cong (_|∨| P⟨xs⟩) (∨-com (P x) (P y)) ; ∨-assoc (P y) (P x) P⟨xs⟩
    alg P .snd .c-dup x _ P⟨xs⟩ = sym (∨-assoc (P x) (P x) P⟨xs⟩) ; cong (_|∨| P⟨xs⟩) (∨-idem (P x))

  Any-𝒦? : ∀ {p} {P : A → Ω p} (P? : ∀ x → Dec (P x .ProofOf)) → ∀ xs → Dec (Any-𝒦 P xs .ProofOf)
  Any-𝒦? P? = ⟦ alg P? ⟧
    where
    alg : ∀ {p} {P : A → Ω p} (P? : ∀ x → Dec (P x .ProofOf)) → Ψ[  xs ⦂ 𝒦 A ] ↦ Dec (Any-𝒦 P xs .ProofOf)
    alg P? .snd = prop-coh λ xs → isPropDec (Any-𝒦 _ xs .IsProp)
    alg P? .fst ∅ = no λ ()
    alg P? .fst (x ∷ _ ⟨ P⟨xs⟩ ⟩) with P? x
    alg P? .fst (x ∷ _ ⟨ _ ⟩) | yes Px = yes ∣ inl Px ∣
    alg P? .fst (x ∷ _ ⟨ yes P⟨xs⟩ ⟩) | _ = yes ∣ inr P⟨xs⟩ ∣
    alg P? .fst (x ∷ _ ⟨ no ¬P⟨xs⟩ ⟩) | no ¬Px = no (∥rec∥ isProp⊥ (¬Px ▿ ¬P⟨xs⟩))

  Any-𝒦-∈ : ∀ {p} (P : A → Ω p) → ∀ xs → ProofOf (Any-𝒦 P xs) → ∥ ∃ x × x ∈ xs × ProofOf (P x) ∥
  Any-𝒦-∈ P = ⟦ alg P ⟧
    where
    alg : ∀ {p} (P : A → Ω p) → Ψ[ xs ⦂ 𝒦 A ] ↦ (ProofOf (Any-𝒦 P xs) → ∥ ∃ x × x ∈ xs × ProofOf (P x) ∥)
    alg P .snd = prop-coh (λ xs → isProp→ squash)
    alg P .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = ∥rec∥ squash ((∣_∣ ∘ (x ,_) ∘ (∣ inl ∣ refl ∣ ∣ ,_)) ▿ ∥map∥ (map₂ (map₁ (there x xs)) ) ∘ P⟨xs⟩)

  ∈-Any-𝒦 : ∀ {p} (P : A → Ω p) → ∀ x → ProofOf (P x) → ∀ xs → x ∈ xs → Any-𝒦 P xs .ProofOf
  ∈-Any-𝒦 P x Px = ⟦ alg P x Px ⟧
    where
    alg : ∀ {p} (P : A → Ω p) → ∀ x → ProofOf (P x) → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ xs → Any-𝒦 P xs .ProofOf)
    alg P x Px .snd = prop-coh λ xs → isProp→ (IsProp (Any-𝒦 P xs))
    alg P x Px .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) =
      ∥rec∥ (IsProp (Any-𝒦 P (y ∷ xs)))
        (∥rec∥ (IsProp (Any-𝒦 P (y ∷ xs))) (∣_∣ ∘ inl ∘ flip (subst (ProofOf ∘ P)) Px ) ▿ ∣_∣ ∘ inr ∘ P⟨xs⟩)

  isProp-⊆ : (xs ys : 𝒦 A) → isProp (xs ⊆ ys)
  isProp-⊆ xs ys = isPropΠ (λ x → isProp→ (isProp-∈ x ys))

open import HITs.PropositionalTruncation

opaque
  here : (x : A) (xs : 𝒦 A) → x ∈ x ∷ xs
  here x xs = ∣ inl ∣ refl { x = x } ∣ ∣

module _ {A : Type a} {B : Type b} where
  map-with-∈ : (xs : 𝒦 A) → (∀ x → x ∈ xs → B) → 𝒦 B
  map-with-∈ = ⟦ alg ⟧
      where
      alg : Ψ[ xs ⦂ 𝒦 A ] ↦ ((∀ x → x ∈ xs → B) → 𝒦 B)
      alg .fst ∅ f = ∅
      alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) f = f x (here x xs) ∷ P⟨xs⟩ λ y y∈xs → f y (there x xs y∈xs)
      alg .snd .c-trunc xs = isSetΠ λ _ → trunc
      alg .snd .c-dup x xs P⟨xs⟩ = 
        J (λ ys x∷x∷xs≡ys → (x∈ys : x ∈ ys) (y∈ys : ∀ y → y ∈ xs → y ∈ ys) →
          PathP
            (λ i → ((x : A) → x ∈ x∷x∷xs≡ys i → B) → 𝒦 B)
            (λ f → f x (here x (x ∷ xs)) ∷ f x (there x (x ∷ xs) (here x xs)) ∷ P⟨xs⟩ λ y y∈xs → f y (there x (x ∷ xs) (there x xs y∈xs)))
            (λ f → f x x∈ys ∷ P⟨xs⟩ λ y y∈xs → f y (y∈ys y y∈xs)))
            (λ x∈ys y∈ys → funExt λ f →  
              cong₃ (λ a b c → f x a ∷ f x b ∷ P⟨xs⟩ λ y y∈xs → f y (c y y∈xs))
                {z′ = y∈ys}
                (isProp-∈ x (x ∷ x ∷ xs) (here x (x ∷ xs)) x∈ys)
                (isProp-∈ x (x ∷ x ∷ xs) (there x (x ∷ xs) (here x xs)) x∈ys)
                (funExt λ y → funExt λ y∈xs → isProp-∈ y (x ∷ x ∷ xs) (there x (x ∷ xs) (there x xs y∈xs)) (y∈ys y y∈xs))
                ; dup (f x x∈ys) (P⟨xs⟩ (λ y y∈xs → f y (y∈ys y y∈xs)))
                )
            (dup x xs)
            (here x xs)
            (λ _ → there x xs)
      alg .snd .c-com x y xs P⟨xs⟩ =
        J (λ ys x∷y∷xs≡ys → (y∈ys : y ∈ ys) (x∈ys : x ∈ ys) (z∈ys : ∀ z → z ∈ xs → z ∈ ys) →
          PathP
            (λ i → ((x : A) → x ∈ x∷y∷xs≡ys i → B) → 𝒦 B)
            (λ f → f x (here x (y ∷ xs)) ∷ f y (there x (y ∷ xs) (here y xs)) ∷ P⟨xs⟩ λ z z∈xs → f z (there x (y ∷ xs) (there y xs z∈xs)) )
            (λ f → f y y∈ys ∷ f x x∈ys ∷ P⟨xs⟩ λ z z∈xs → f z (z∈ys z z∈xs))
          )
          (λ y∈ys x∈ys z∈ys → funExt λ f →
            cong₃
              (λ a b c → f x a ∷ f y b ∷ P⟨xs⟩ (λ z z∈xs → f z (c z z∈xs)))
              {z′ = z∈ys}
              (isProp-∈ x (x ∷ y ∷ xs) (here x (y ∷ xs)) x∈ys)
              (isProp-∈ y (x ∷ y ∷ xs) (there x (y ∷ xs) (here y xs)) y∈ys)
              (funExt λ z → funExt λ z∈xs → isProp-∈ z (x ∷ y ∷ xs) (there x (y ∷ xs) (there y xs z∈xs)) (z∈ys z z∈xs))
              ; comm (f x x∈ys) (f y y∈ys) (P⟨xs⟩ (λ z z∈xs → f z (z∈ys z z∈xs)))
          )
          (comm x y xs)
          (here y (x ∷ xs))
          (there y (x ∷ xs) (here x xs))
          (λ z → there y (x ∷ xs) ∘ there x xs)

  map-with-∈-map : ∀ (f : A → B) xs → map-with-∈ xs (λ x x∈xs → f x) ≡ 𝒦-map f xs
  map-with-∈-map f = ⟦ alg f ⟧
    where
    alg : (f : A → B) → Ψ[ xs ⦂ 𝒦 A ] ↦ (map-with-∈ xs (λ x x∈xs → f x) ≡ 𝒦-map f xs)
    alg f .snd = eq-coh
    alg f .fst ∅ = refl
    alg f .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (f x ∷_) P⟨xs⟩
 

∈-map-𝒦 : ∀ (f : A → B) x xs → x ∈ xs → f x ∈ 𝒦-map f xs
∈-map-𝒦 f x = ⟦ alg f x ⟧
  where
  alg : ∀ (f : A → B) x → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ xs → f x ∈ 𝒦-map f xs)
  alg f x .snd = prop-coh λ xs → isProp→ (isProp-∈ (f x) (𝒦-map f xs))
  alg f x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) = ∥map∥ (map-⊎ (∥map∥ (cong f)) P⟨xs⟩)

∈-map-ind-𝒦 : ∀ (xs : 𝒦 A) (f : ∀ x → x ∈ xs → B) y → (y∈xs : y ∈ xs) → f y y∈xs ∈ map-with-∈ xs f
∈-map-ind-𝒦 xs f y = ⟦ alg y ⟧ xs f
  where
  opaque
    unfolding there
    alg : ∀ y → Ψ[ xs ⦂ 𝒦 A ] ↦ (∀ (f : ∀ x → x ∈ xs → B) → (y∈xs : y ∈ xs) → f y y∈xs ∈ map-with-∈ xs f)
    alg y .snd = prop-coh λ xs → isPropΠ λ f → isPropΠ λ y∈xs → isProp-∈ (f y y∈xs) (map-with-∈ xs f)
    alg y .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) f =
      ∥elim∥
        (λ y∈xs → isProp-∈ (f y y∈xs) (map-with-∈ (x ∷ xs) f))
        λ { (inl ∣y≡x∣) → ∥rec∥ (isProp-∈ (f y ∣ inl ∣y≡x∣ ∣) (map-with-∈ (x ∷ xs) f)) (λ y≡x → ∣ inl ∣ cong (uncurry f) (Σ≡Prop (λ y → isProp-∈ y (x ∷ xs)) y≡x) ∣ ∣) ∣y≡x∣
          ; (inr y∈xs) → there (f x (here x xs)) (map-with-∈ xs _) (P⟨xs⟩ (λ z z∈xs → f z (there x xs z∈xs)) y∈xs)
          }

∈-map-inv-𝒦 : ∀ (f : A ↣ B) x xs → fst f x ∈ 𝒦-map (fst f) xs → x ∈ xs
∈-map-inv-𝒦 f x = ⟦ alg f x ⟧
  where
  alg : ∀ (f : A ↣ B) x → Ψ[ xs ⦂ 𝒦 A ] ↦ (fst f x ∈ 𝒦-map (fst f) xs → x ∈ xs)
  alg f x .snd = prop-coh λ xs → isProp→ (isProp-∈ x xs)
  alg f x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) = ∥map∥ (map-⊎ (∥map∥ (f .snd)) P⟨xs⟩)

∈-map-surj : ∀ (f : A → B) x xs → x ∈ 𝒦-map f xs → ∥ Surjected f x ∥
∈-map-surj f x = ⟦ alg f x ⟧
  where
  alg : ∀ (f : A → B) x → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ 𝒦-map f xs → ∥ Surjected f x ∥)
  alg f x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) = ∥rec∥ squash (∥map∥ ((y ,↠_) ∘ sym) ▿ P⟨xs⟩)
  alg f x .snd = prop-coh λ xs → isProp→ squash

_>>=_ : 𝒦 A → (A → 𝒦 B) → 𝒦 B
xs >>= k = ⟦ bind-alg k ⟧ xs
  where
  bind-alg : (A → 𝒦 B) → Ψ[ xs ⦂ 𝒦 A ] ↦ 𝒦 B
  bind-alg k .fst ∅ = ∅
  bind-alg k .fst (x ∷ _ ⟨ xs ⟩) = k x ∪ xs
  bind-alg k .snd .c-trunc _ = trunc
  bind-alg k .snd .c-com x y _ xs =
    k x ∪ k y ∪ xs ≡˘⟨ ∪-assoc (k x) (k y) xs ⟩
    (k x ∪ k y) ∪ xs ≡⟨ cong (_∪ xs) (∪-com (k x) (k y)) ⟩
    (k y ∪ k x) ∪ xs ≡⟨ ∪-assoc (k y) (k x) xs ⟩
    k y ∪ k x ∪ xs ∎
  bind-alg k .snd .c-dup x _ xs =
    k x ∪ k x ∪ xs ≡˘⟨ ∪-assoc (k x) (k x) xs ⟩
    (k x ∪ k x) ∪ xs ≡⟨ cong (_∪ xs) (∪-idem (k x)) ⟩
    k x ∪ xs ∎

open import HITs.PropositionalTruncation

∈->>= : ∀ (x : A) (y : B)
      → (k : A → 𝒦 B)
      → (y ∈ k x)
      → (xs : 𝒦 A)
      → x ∈ xs
      → y ∈ (xs >>= k)
∈->>= x y k fx∈kx = ⟦ alg x y k fx∈kx ⟧
  where
  alg : ∀ (x : A) (y : B) (k : A → 𝒦 B) → y ∈ k x → Ψ[ xs ⦂ 𝒦 A ] ↦ (x ∈ xs → y ∈ (xs >>= k))
  alg x y k y∈kx .snd = prop-coh λ xs → isProp→ (isProp-∈ y (xs >>= k))
  alg x y k y∈kx .fst (z ∷ xs ⟨ P⟨xs⟩ ⟩) =
    ∥rec∥
      (isProp-∈ y ((z ∷ xs) >>= k))
      (∥rec∥ (isProp-∈ y ((z ∷ xs) >>= k)) (λ x≡z → ∈-∪ˡ (k z) (xs >>= k) (subst (λ e → y ∈ k e) x≡z y∈kx))
      ▿ ∈-∪ʳ (k z) (xs >>= k) ∘ P⟨xs⟩)
