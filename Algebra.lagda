\begin{code}
{-# OPTIONS --cubical --safe #-}
module Algebra where

open import Prelude

module _ {a} {A : Type a} (_∙_ : A → A → A) where
  Associative : Type a
  Associative = ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

  Commutative : Type _
  Commutative = ∀ x y → x ∙ y ≡ y ∙ x

  Idempotent : Type _
  Idempotent = ∀ x → x ∙ x ≡ x

Identityˡ : (A → B → B) → A → Type _
Identityˡ _∙_ x = ∀ y → x ∙ y ≡ y

Zeroˡ : (A → B → A) → A → Type _
Zeroˡ _∙_ x = ∀ y → x ∙ y ≡ x

Zeroʳ : (A → B → B) → B → Type _
Zeroʳ _∙_ x = ∀ y → y ∙ x ≡ x

Identityʳ : (A → B → A) → B → Type _
Identityʳ _∙_ x = ∀ y → y ∙ x ≡ y

_Distributesʳ_ : (A → B → B) → (B → B → B) → Type _
_⊗_ Distributesʳ _⊕_ = ∀ x y z → x ⊗ (y ⊕ z) ≡ (x ⊗ y) ⊕ (x ⊗ z)

_Distributesˡ_ : (B → A → B) → (B → B → B) → Type _
_⊗_ Distributesˡ _⊕_ = ∀ x y z → (x ⊕ y) ⊗ z ≡ (x ⊗ z) ⊕ (y ⊗ z)

Cancellableˡ : (A → B → C) → A → Type _
Cancellableˡ _⊗_ c = ∀ x y → c ⊗ x ≡ c ⊗ y → x ≡ y

Cancellableʳ : (A → B → C) → B → Type _
Cancellableʳ _⊗_ c = ∀ x y → x ⊗ c ≡ y ⊗ c → x ≡ y

Cancellativeˡ : (A → B → C) → Type _
Cancellativeˡ _⊗_ = ∀ c → Cancellableˡ _⊗_ c

Cancellativeʳ : (A → B → C) → Type _
Cancellativeʳ _⊗_ = ∀ c → Cancellableʳ _⊗_ c

module _ {ℓ} (𝑆 : Type ℓ) where
  record  Semigroup : Type ℓ where
    infixl 6 _∙_
    field
      _∙_    : 𝑆 → 𝑆 → 𝑆
      assoc  : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

  module _ {ℓ₂} (P : Type ℓ₂) where
    record RightAction : Type (ℓ ℓ⊔ ℓ₂) where
      infixl 5 _⊢_
      field
        semigroup : Semigroup
      open Semigroup semigroup public
      field
        _⊢_ : P → 𝑆 → P
        ⊢‿assoc : ∀ x s t → x ⊢ s ⊢ t ≡ x ⊢ s ∙ t

  record IdempotentSemigroup : Type ℓ where
    field
      semigroup : Semigroup
    open Semigroup semigroup public
    field
      idem : Idempotent _∙_

  record  Monoid : Type ℓ where
    infixl 6 _∙_
    field
      _∙_    : 𝑆 → 𝑆 → 𝑆
      ε      : 𝑆
      assoc  : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      ε∙     : ∀ x → ε ∙ x ≡ x
      ∙ε     : ∀ x → x ∙ ε ≡ x

    semigroup : Semigroup
    semigroup = record
      { _∙_ = _∙_; assoc = assoc }


  record Group : Type ℓ where
    field
      monoid : Monoid
    open Monoid monoid public
    field
      -_ : 𝑆 → 𝑆
      ∙⁻ : ∀ x → x ∙ - x ≡ ε
      ⁻∙ : ∀ x → - x ∙ x ≡ ε

    open import Path.Reasoning

    cancelˡ : Cancellativeˡ _∙_
    cancelˡ x y z p =
      y ≡˘⟨ ε∙ y ⟩
      ε ∙ y ≡˘⟨ cong (_∙ y) (⁻∙ x) ⟩
      (- x ∙ x) ∙ y ≡⟨ assoc (- x) x y ⟩
      - x ∙ (x ∙ y) ≡⟨ cong (- x ∙_) p ⟩
      - x ∙ (x ∙ z) ≡˘⟨ assoc (- x) x z ⟩
      (- x ∙ x) ∙ z ≡⟨ cong (_∙ z) (⁻∙ x) ⟩
      ε ∙ z ≡⟨ ε∙ z ⟩
      z ∎

    cancelʳ : Cancellativeʳ _∙_
    cancelʳ x y z p =
      y ≡˘⟨ ∙ε y ⟩
      y ∙ ε ≡˘⟨ cong (y ∙_) (∙⁻ x) ⟩
      y ∙ (x ∙ - x) ≡˘⟨ assoc y x (- x) ⟩
      (y ∙ x) ∙ - x ≡⟨ cong (_∙ - x) p ⟩
      (z ∙ x) ∙ - x ≡⟨ assoc z x (- x) ⟩
      z ∙ (x ∙ - x) ≡⟨ cong (z ∙_) (∙⁻ x) ⟩
      z ∙ ε ≡⟨ ∙ε z ⟩
      z ∎

  record CommutativeMonoid : Type ℓ where
    field
      monoid : Monoid
    open Monoid monoid public
    field
      comm : Commutative _∙_

  record Semilattice : Type ℓ where
    field
      commutativeMonoid : CommutativeMonoid
    open CommutativeMonoid commutativeMonoid public
    field
      idem : Idempotent _∙_

  record Weight : Type ℓ where
    infixl 6 _⊕_
    infixl 7 _⊗_
    field
      _⊕_ : 𝑆 → 𝑆 → 𝑆
      _⊗_ : 𝑆 → 𝑆 → 𝑆
      𝟙 : 𝑆
      ⊕-assoc : Associative _⊕_
      ⊗-assoc : Associative _⊗_
      ⊕-com : Commutative _⊕_
      𝟙⊗ : Identityˡ _⊗_ 𝟙
      ⊗𝟙 : Identityʳ _⊗_ 𝟙
      ⟨⊕⟩⊗ : _⊗_ Distributesˡ _⊕_
      ⊗⟨⊕⟩ : _⊗_ Distributesʳ _⊕_

    ⊕-semigroup : Semigroup
    ⊕-semigroup .Semigroup._∙_ = _⊕_
    ⊕-semigroup .Semigroup.assoc = ⊕-assoc

    ⊗-monoid : Monoid
    ⊗-monoid .Monoid._∙_ = _⊗_
    ⊗-monoid .Monoid.ε = 𝟙
    ⊗-monoid .Monoid.assoc = ⊗-assoc
    ⊗-monoid .Monoid.ε∙ = 𝟙⊗
    ⊗-monoid .Monoid.∙ε = ⊗𝟙

  record Semiring : Type ℓ where
    infixl 6 _⊕_
    infixl 7 _⊗_
    field
      _⊕_ : 𝑆 → 𝑆 → 𝑆
      _⊗_ : 𝑆 → 𝑆 → 𝑆
      𝟙 : 𝑆
      𝟘 : 𝑆
      ⊕-assoc : Associative _⊕_
      ⊗-assoc : Associative _⊗_
      𝟘⊕ : Identityˡ _⊕_ 𝟘
      ⊕-com : Commutative _⊕_
      𝟙⊗ : Identityˡ _⊗_ 𝟙
      ⊗𝟙 : Identityʳ _⊗_ 𝟙
      𝟘⊗ : Zeroˡ _⊗_ 𝟘
      ⊗𝟘 : Zeroʳ _⊗_ 𝟘
      ⟨⊕⟩⊗ : _⊗_ Distributesˡ _⊕_
      ⊗⟨⊕⟩ : _⊗_ Distributesʳ _⊕_

    ⊕-monoid : CommutativeMonoid
    ⊕-monoid .CommutativeMonoid.monoid .Monoid._∙_ = _⊕_
    ⊕-monoid .CommutativeMonoid.monoid .Monoid.ε = 𝟘
    ⊕-monoid .CommutativeMonoid.monoid .Monoid.assoc = ⊕-assoc
    ⊕-monoid .CommutativeMonoid.monoid .Monoid.ε∙ = 𝟘⊕
    ⊕-monoid .CommutativeMonoid.monoid .Monoid.∙ε x = ⊕-com x 𝟘 ; 𝟘⊕ x
    ⊕-monoid .CommutativeMonoid.comm = ⊕-com

    ⊗-monoid : Monoid
    ⊗-monoid .Monoid._∙_ = _⊗_
    ⊗-monoid .Monoid.ε = 𝟙
    ⊗-monoid .Monoid.assoc = ⊗-assoc
    ⊗-monoid .Monoid.ε∙ = 𝟙⊗
    ⊗-monoid .Monoid.∙ε = ⊗𝟙

\end{code}
%<*exp>
\begin{code}
    exp : 𝑆 → ℕ → 𝑆 
    exp x zero     = 𝟙
    exp x (suc n)  = x ⊗ exp x n
\end{code}
%</exp>
\begin{code}

--   record IdempotentSemiring : Type ℓ where
--     field
--       semiring : Semiring
--     open Semiring semiring public
--     field
--       +-idem : Idempotent _+_

--   record CommutativeSemiring : Type ℓ where
--     field
--       semiring : Semiring
--     open Semiring semiring public
--     field
--       *-comm : Commutative _*_

  record StarSemiring : Type ℓ where
    field semiring : Semiring
    open Semiring semiring public
    field
      _∗ : 𝑆 → 𝑆
      star-iterʳ : ∀ x →
\end{code}
%<*star-iter-r>
\begin{code}
        x ∗ ≡ 𝟙 ⊕ (x ⊗ x ∗)
\end{code}
%</star-iter-r>
\begin{code}
      star-iterˡ : ∀ x →
\end{code}
%<*star-iter-l>
\begin{code}
        x ∗ ≡ 𝟙 ⊕ (x ∗ ⊗ x)
\end{code}
%</star-iter-l>
\begin{code}
    _⁺ : 𝑆 → 𝑆
    x ⁺ = x ⊗ x ∗

record LeftSemimodule {ℓ₁ ℓ₂} {𝑆 : Type ℓ₁} (semiring : Semiring 𝑆) (𝑉 : Type ℓ₂) : Type (ℓ₁ ℓ⊔ ℓ₂) where
  open Semiring semiring public
  field semimodule : CommutativeMonoid 𝑉
  open CommutativeMonoid semimodule renaming (_∙_ to _∪_) public
    renaming ( assoc to ∪-assoc
             ; comm to ∪-com
             ; ε∙ to ∅∪
             ; ∙ε to ∪∅
             ; ε to ∅
             )
  infixr 7 _⋊_
  field
    _⋊_ : 𝑆 → 𝑉 → 𝑉
    ⟨*⟩⋊ : ∀ x y z → (x ⊗ y) ⋊ z ≡ x ⋊ (y ⋊ z)
    ⟨+⟩⋊ : ∀ x y z → (x ⊕ y) ⋊ z ≡ (x ⋊ z) ∪ (y ⋊ z)
    ⋊⟨∪⟩ : _⋊_ Distributesʳ _∪_
    1⋊ : Identityˡ _⋊_ 𝟙
    0⋊ : ∀ x → 𝟘 ⋊ x ≡ ∅
    ⋊∅ : ∀ x → x ⋊ ∅ ≡ ∅

record WeightSemimodule {ℓ₁ ℓ₂} {𝑆 : Type ℓ₁} (weight : Weight 𝑆) (𝑉 : Type ℓ₂) : Type (ℓ₁ ℓ⊔ ℓ₂) where
  open Weight weight public
  field semimodule : CommutativeMonoid 𝑉
  open CommutativeMonoid semimodule
    renaming ( _∙_ to _∪_
             ; assoc to ∪-assoc
             ; ε∙ to ∅∪
             ; ∙ε to ∪∅
             ; ε to ∅
             ; comm to ∪-com
             )
    public
  infixr 7 _⋊_
  field
    _⋊_ : 𝑆 → 𝑉 → 𝑉
    ⟨*⟩⋊ : ∀ x y z → (x ⊗ y) ⋊ z ≡ x ⋊ (y ⋊ z)
    ⟨+⟩⋊ : ∀ x y z → (x ⊕ y) ⋊ z ≡ (x ⋊ z) ∪ (y ⋊ z)
    ⋊⟨∪⟩ : _⋊_ Distributesʳ _∪_
    1⋊ : Identityˡ _⋊_ 𝟙
    ⋊∅ : ∀ x → x ⋊ ∅ ≡ ∅

record MonoidHomomorphism_⟶_
        {ℓ₁ ℓ₂} {𝑆 : Type ℓ₁} {𝑇 : Type ℓ₂}
        (from : Monoid 𝑆)
        (to   : Monoid 𝑇)
      : Type (ℓ₁ ℓ⊔ ℓ₂) where
  open Monoid from
  open Monoid to
    renaming ( _∙_ to _⊙_
             ; ε to ⓔ)
  field
    f : 𝑆 → 𝑇
    ∙-homo : ∀ x y → f (x ∙ y) ≡ f x ⊙ f y
    ε-homo : f ε ≡ ⓔ

record SemimoduleHomomorphism[_]_⟶_
        {ℓ₁ ℓ₂ ℓ₃} {𝑆 : Type ℓ₁} {𝑉₁ : Type ℓ₂} {𝑉₂ : Type ℓ₃}
        (rng : Semiring 𝑆)
        (from : LeftSemimodule rng 𝑉₁)
        (to : LeftSemimodule rng 𝑉₂) : Type (ℓ₁ ℓ⊔ ℓ₂ ℓ⊔ ℓ₃) where

  open Semiring rng
  open LeftSemimodule from using (_⋊_; monoid)
  open LeftSemimodule to using () renaming (_⋊_ to _⋊′_; monoid to monoid′)

  field mon-homo : MonoidHomomorphism monoid ⟶ monoid′

  open MonoidHomomorphism_⟶_ mon-homo public

  field ⋊-homo : ∀ r x → f (r ⋊ x) ≡ r ⋊′ f x

record WeightHomomorphism[_]_⟶_
        {ℓ₁ ℓ₂ ℓ₃} {𝑆 : Type ℓ₁} {𝑉₁ : Type ℓ₂} {𝑉₂ : Type ℓ₃}
        (rng : Weight 𝑆)
        (from : WeightSemimodule rng 𝑉₁)
        (to : WeightSemimodule rng 𝑉₂) : Type (ℓ₁ ℓ⊔ ℓ₂ ℓ⊔ ℓ₃) where

  open Weight rng
  open WeightSemimodule from using (_⋊_; monoid)
  open WeightSemimodule to using () renaming (_⋊_ to _⋊′_; monoid to monoid′)

  field mon-homo : MonoidHomomorphism monoid ⟶ monoid′

  open MonoidHomomorphism_⟶_ mon-homo public

  field ⋊-homo : ∀ r x → f (r ⋊ x) ≡ r ⋊′ f x


module _ {ℓ₁ ℓ₂} (F : Type ℓ₁ → Type ℓ₂) where

  record Functor : Type (ℓsuc ℓ₁ ℓ⊔ ℓ₂) where
    field
      map : (A → B) → F A → F B
      map-id : (x : F A) → map id x ≡ x
      map-comp :  (f : B → C) (g : A → B) (x : F A) →  map f (map g x) ≡ map (f ∘ g) x

  record Monad : Type (ℓsuc ℓ₁ ℓ⊔ ℓ₂) where
    infixl 1 _>>=_
    field
      _>>=_ : F A → (A → F B) → F B
      return : A → F A

      >>=-idˡ : (f : A → F B) → (x : A) → (return x >>= f) ≡ f x
      >>=-idʳ : (x : F A) → (x >>= return) ≡ x
      >>=-assoc : (xs : F A) (f : A → F B) (g : B → F C) → ((xs >>= f) >>= g) ≡ (xs >>= (λ x → f x >>= g))

    mmap : (A → B) → F A → F B
    mmap f xs = xs >>= (return ∘ f)

    infixr 3 _>=>_
    _>=>_ : (A → F B) → (B → F C) → A → F C
    (xs >=> ys) x = xs x >>= ys

    open import Path.Reasoning

    mmap-comp : (f : B → C) (g : A → B) (x : F A) → mmap f (mmap g x) ≡ mmap (f ∘ g) x
    mmap-comp f g x =
      mmap f (mmap g x) ≡⟨⟩
      ((x >>= return ∘ g) >>= return ∘ f) ≡⟨ >>=-assoc x (return ∘ g) (return ∘ f) ⟩
      (x >>= λ x′ → return (g x′) >>= return ∘ f) ≡⟨ cong (x >>=_) (funExt λ x′ → >>=-idˡ (return ∘ f) (g x′)) ⟩
      mmap (f ∘ g) x ∎


  record Comonad : Type (ℓsuc ℓ₁ ℓ⊔ ℓ₂) where
    field
      extend : (F A → B) → F A → F B
      extract : F A → A

    infixl 1 _=>>_
    _=>>_ : F A → (F A → B) → F B
    _=>>_ = flip extend

    cmap : (A → B) → F A → F B
    cmap f xs = xs =>> (f ∘ extract)

  record ComMonadPlus : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
    field
      monad : Monad
    open Monad monad public
    field
      empty : F A
      _<|>_ : F A → F A → F A
      <|>-idˡ : (x : F A) → empty <|> x ≡ x
      <|>-assoc : (x y z : F A) → (x <|> y) <|> z ≡ x <|> (y <|> z)
      <|>-com : (x y : F A) → x <|> y ≡ y <|> x
      >>=-annˡ : (x : A → F B) → (empty >>= x) ≡ empty
      >>=-annʳ : (x : F A) → (x >>= const empty) ≡ empty {A = B}
      <|>-distribˡ : (x y : F A) → (z : A → F B) → ((x <|> y) >>= z) ≡ (x >>= z) <|> (y >>= z)
      <|>-distribʳ : (x : F A) → (y z : A → F B) → (x >>= (λ x′ → y x′ <|> z x′)) ≡ (x >>= y) <|> (x >>= z)

    module ArrSemiring {A : Type ℓ₁} where
      S : Type _
      S = A → F A

      _⊕_ : S → S → S
      (f ⊕ g) x = f x <|> g x

      _⊗_ : S → S → S
      (f ⊗ g) x = f x >>= g

      𝟙 : S
      𝟙 = return

      𝟘 : S
      𝟘 _ = empty

      ⊕-assoc : Associative _⊕_
      ⊕-assoc x y z = funExt λ p → <|>-assoc (x p) (y p) (z p)

      ⊗-assoc : Associative _⊗_
      ⊗-assoc x y z = funExt λ p → >>=-assoc (x p) y z

      ⊕-com : Commutative _⊕_
      ⊕-com x y = funExt λ p → <|>-com (x p) (y p)

      𝟙⊗ : Identityˡ _⊗_ 𝟙
      𝟙⊗ x = funExt λ p → >>=-idˡ x p

      ⊗𝟙 : Identityʳ _⊗_ 𝟙
      ⊗𝟙 x = funExt λ p → >>=-idʳ (x p)

      ⟨⊕⟩⊗ : _⊗_ Distributesˡ _⊕_
      ⟨⊕⟩⊗ x y z = funExt λ p → <|>-distribˡ (x p) (y p) z

      ⊗⟨⊕⟩ : _⊗_ Distributesʳ _⊕_
      ⊗⟨⊕⟩ x y z = funExt λ p → <|>-distribʳ (x p) y z

      𝟘⊕ : Identityˡ _⊕_ 𝟘
      𝟘⊕ x = funExt λ p → <|>-idˡ (x p)

      𝟘⊗ : Zeroˡ _⊗_ 𝟘
      𝟘⊗ x = funExt λ p → >>=-annˡ x

      ⊗𝟘 : Zeroʳ _⊗_ 𝟘
      ⊗𝟘 x = funExt λ p → >>=-annʳ (x p)


    arr-semiring : Semiring (A → F A)
    arr-semiring {A = A} = record { ArrSemiring {A = A} }
\end{code}
