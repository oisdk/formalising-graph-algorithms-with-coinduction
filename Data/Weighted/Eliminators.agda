{-# OPTIONS --safe #-}

open import Algebra
open import Prelude

module Data.Weighted.Eliminators {ℓ} {𝑆 : Type ℓ} (sgp : Semigroup 𝑆) where

open Semigroup sgp
open import Data.Weighted.Definition sgp
open import Data.Weighted.Functor

𝔚 : (A : Type a) (P : Weighted A → Type p) → Type (a ℓ⊔ p ℓ⊔ ℓ)
𝔚 A = 𝔚-F 𝑆 (Weighted A) A



⟪_⟫ : 𝔚 A P → Weighted A
⟪ ⟅⟆ ⟫ = ⟅⟆
⟪ w ▹ x ∷ xs ⟨ P⟨xs⟩ ⟩ ⟫ = w ▹ x ∷ xs

Alg : (A : Type a) (P : Weighted A → Type p) → Type _
Alg A P = (xs : 𝔚 A P) → P ⟪ xs ⟫

module _ {A : Type a} {P : Weighted A → Type p} where
  record Coherent (ψ : Alg A P) : Type (p ℓ⊔ a ℓ⊔ ℓ) where
    field  c-set : ∀ xs → isSet (P xs)
           c-dup : ∀ p q x xs ψ⟨xs⟩ →
             PathP
               (λ i → P (dup p q x xs i))
               (ψ (p  ▹ x ∷ (q ▹ x ∷ xs) ⟨ ψ (q ▹ x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩))
               (ψ ((p ∙ q) ▹ x ∷ xs ⟨ ψ⟨xs⟩ ⟩))
           c-com : ∀ p x q y xs ψ⟨xs⟩ →
             PathP
               (λ i → P (com p x q y xs i))
               (ψ (p  ▹ x ∷ (q ▹ y ∷ xs) ⟨ ψ (q ▹ y ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩))
               (ψ (q ▹ y ∷ (p ▹ x ∷ xs) ⟨ ψ (p ▹ x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩))
open Coherent public

Ψ :  (A : Type a) (P : Weighted A → Type p) →
     Type _
Ψ A P = Σ (Alg A P) Coherent

infixr 1 Ψ
syntax Ψ A (λ v → e) = Ψ[ v ⦂ Weighted A ] ↦ e

Φ : Type a → Type b → Type (a ℓ⊔ b ℓ⊔ ℓ)
Φ A B = Ψ A (λ _ → B)

⟦_⟧ : Ψ A P → (xs : Weighted A) → P xs
⟦ alg ⟧ ⟅⟆                    = alg .fst ⟅⟆
⟦ alg ⟧ (p ▹ x ∷ xs)          = alg .fst (p ▹ x ∷ xs ⟨ ⟦ alg ⟧ xs ⟩)
⟦ alg ⟧ (dup p q x xs i)      = alg .snd .c-dup p q x xs (⟦ alg ⟧ xs) i
⟦ alg ⟧ (com p x q y xs i)    = alg .snd .c-com p x q y xs (⟦ alg ⟧ xs) i
⟦ alg ⟧ (trunc xs ys p q i j) =
  isOfHLevel→isOfHLevelDep 2
    (alg .snd .c-set)
    (⟦ alg ⟧ xs) (⟦ alg ⟧ ys)
    (cong ⟦ alg ⟧ p) (cong ⟦ alg ⟧ q)
    (trunc xs ys p q)
    i j

prop-coh : {A : Type a} {P : Weighted A → Type p} {alg : Alg A P} → (∀ xs → isProp (P xs)) → Coherent alg
prop-coh P-isProp .c-set xs = isProp→isSet (P-isProp xs)
prop-coh {P = P} {alg = alg} P-isProp .c-dup p q x xs ψ⟨xs⟩ =
 toPathP (P-isProp (p ∙ q ▹ x ∷ xs) (transp (λ i → P (dup p q x xs i)) i0 (alg (p ▹ x ∷ (q ▹ x ∷ xs) ⟨ alg (q ▹ x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩))) (alg ((p ∙ q) ▹ x ∷ xs ⟨ ψ⟨xs⟩ ⟩)))
prop-coh {P = P} {alg = alg} P-isProp .c-com p x q y xs ψ⟨xs⟩ =
  toPathP (P-isProp (q ▹ y ∷ p ▹ x ∷ xs) (transp (λ i → P (com p x q y xs i)) i0 (alg (p ▹ x ∷ (q ▹ y ∷ xs) ⟨ alg (q ▹ y ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩))) (alg (q ▹ y ∷ (p ▹ x ∷ xs) ⟨ alg (p ▹ x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩)))

infix 4 _⊜_
record AnEquality (A : Type a) : Type (a ℓ⊔ ℓ) where
  constructor _⊜_
  field lhs rhs : Weighted A
open AnEquality

EqualityProof-Alg : {B : Type b} (A : Type a) (P : Weighted A → AnEquality B) → Type (a ℓ⊔ b ℓ⊔ ℓ)
EqualityProof-Alg A P = Alg A (λ xs → let Pxs = P xs in lhs Pxs ≡ rhs Pxs)

eq-coh : {A : Type a} {B : Type b} {P : Weighted A → AnEquality B} {alg : EqualityProof-Alg A P} → Coherent alg
eq-coh {P = P} = prop-coh λ xs → let Pxs = P xs in trunc (lhs Pxs) (rhs Pxs)

record _W⟶_ (A : Type a) (B : Type b) : Type (ℓ ℓ⊔ a ℓ⊔ b) where
  no-eta-equality
  field
    w-mon : CommutativeMonoid B
    w-set : isSet B
  open CommutativeMonoid w-mon
    using ()
    renaming
      ( assoc to W[_]-assoc
      ; ε to W[_]-ε
      ; comm to W[_]-comm
      ; ε∙ to W[_]-ε∙
      ; ∙ε to W[_]-∙ε
      ) public

  open CommutativeMonoid w-mon using () renaming (_∙_ to _⊕_)

  field
    w-act : 𝑆 → A → B
    w-coh : ∀ p q x → w-act p x ⊕ w-act q x ≡ w-act (p ∙ q) x

open _W⟶_ public

infixl 6 _W[_]⊣_
_W[_]⊣_ : 𝑆 → A W⟶ B → A → B
w W[ h ]⊣ x = w-act h w x

infixl 6 _W[_]⊕_
_W[_]⊕_ : B → A W⟶ B → B → B
x W[ h ]⊕ y = Monoid._∙_ (CommutativeMonoid.monoid (w-mon h)) x y

module _ {A : Type a} {B : Type b} where
  W[_]↓ : A W⟶ B → Weighted A → B
  W[ h ]↓ = ⟦ f-alg ⟧
    where
    f-alg : Ψ[ xs ⦂ Weighted A ] ↦ B
    f-alg .fst ⟅⟆ = W[ h ]-ε
    f-alg .fst (v ▹ x ∷ _ ⟨ xs ⟩) = v W[ h ]⊣ x W[ h ]⊕ xs
    f-alg .snd .c-set _ = w-set h
    f-alg .snd .c-com p x q y _ xs = sym (W[ h ]-assoc (p W[ h ]⊣ x) (q W[ h ]⊣ y) xs) ; cong (_W[ h ]⊕ xs) (W[ h ]-comm (p W[ h ]⊣ x) (q W[ h ]⊣ y)) ; W[ h ]-assoc (q W[ h ]⊣ y) (p W[ h ]⊣ x) xs
    f-alg .snd .c-dup p q x _   xs = sym (W[ h ]-assoc (p W[ h ]⊣ x) (q W[ h ]⊣ x) xs) ; cong (_W[ h ]⊕ xs) (w-coh h p q x)

module W⟶-Eq {A : Type a} {B : Type b} where
  W⟶′ : Type _
  W⟶′ = Σ[ act-cmb-emt ⦂ ((𝑆 → A → B) × (B → B → B) × B) ]
       × (let (act , cmb , emt) = act-cmb-emt in
       isSet B
       × Associative cmb
       × Commutative cmb
       × (∀ x → cmb emt x ≡ x)
       × (∀ x → cmb x emt ≡ x)
       × (∀ p q x → cmb (act p x) (act q x) ≡ act (p ∙ q) x))

  toSigma : (A W⟶ B) → W⟶′
  toSigma a→b = (_W[ a→b ]⊣_ , _W[ a→b ]⊕_ , W[ a→b ]-ε) , w-set a→b , W[ a→b ]-assoc , W[ a→b ]-comm , W[ a→b ]-ε∙ , W[ a→b ]-∙ε , w-coh a→b

  fromSigma : W⟶′ → (A W⟶ B)
  fromSigma ((act , cmb , emt) , isSetB , assoc′ , comm′ , iden′ , iden″ , coh′) = record
    { w-mon = record
      { monoid = record
        { _∙_ = cmb
        ; ε = emt
        ; assoc = assoc′
        ; ε∙ = iden′
        ; ∙ε = iden″
        }
      ; comm   = comm′
      }
    ; w-set = isSetB
    ; w-act = act
    ; w-coh = coh′
    }

  sigma-iso : (A W⟶ B) ⇔ W⟶′
  sigma-iso .fun = toSigma
  sigma-iso .inv = fromSigma
  sigma-iso .rightInv x = refl
  sigma-iso .leftInv alg i .w-mon .CommutativeMonoid.monoid .Monoid._∙_ = alg ._W⟶_.w-mon .CommutativeMonoid.monoid .Monoid._∙_
  sigma-iso .leftInv alg i .w-mon .CommutativeMonoid.monoid .Monoid.ε = alg ._W⟶_.w-mon .CommutativeMonoid.monoid .Monoid.ε
  sigma-iso .leftInv alg i .w-mon .CommutativeMonoid.monoid .Monoid.assoc = alg ._W⟶_.w-mon .CommutativeMonoid.monoid .Monoid.assoc
  sigma-iso .leftInv alg i .w-mon .CommutativeMonoid.monoid .Monoid.ε∙ = alg ._W⟶_.w-mon .CommutativeMonoid.monoid .Monoid.ε∙
  sigma-iso .leftInv alg i .w-mon .CommutativeMonoid.monoid .Monoid.∙ε = alg ._W⟶_.w-mon .CommutativeMonoid.monoid .Monoid.∙ε
  sigma-iso .leftInv alg i .w-mon .CommutativeMonoid.comm = alg ._W⟶_.w-mon .CommutativeMonoid.comm
  sigma-iso .leftInv alg i .w-set = alg ._W⟶_.w-set
  sigma-iso .leftInv alg i .w-act = alg ._W⟶_.w-act
  sigma-iso .leftInv alg i .w-coh = alg ._W⟶_.w-coh

  open import Cubical.Data.Sigma
  open import Cubical.Foundations.HLevels using (isProp×; isProp×5; isPropIsSet)

  W⟶-≡ : (x y : A W⟶ B)
        → (∀ w v → x ._W⟶_.w-act w v ≡ y ._W⟶_.w-act w v)
        → (∀ w v → x ._W⟶_.w-mon .CommutativeMonoid.monoid .Monoid._∙_ w v ≡ y ._W⟶_.w-mon .CommutativeMonoid.monoid .Monoid._∙_ w v)
        → (x ._W⟶_.w-mon .CommutativeMonoid.monoid .Monoid.ε ≡ y ._W⟶_.w-mon .CommutativeMonoid.monoid .Monoid.ε)
        → x ≡ y
  W⟶-≡ x y p q r = sym (sigma-iso .leftInv x)
              ; cong fromSigma (Σ≡Prop
                (λ _ → isProp× isPropIsSet ( isProp× (isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → x ._W⟶_.w-set _ _)
                                           (isProp× (isPropΠ λ _ → isPropΠ λ _ → x ._W⟶_.w-set _ _)
                                           (isProp× (isPropΠ λ _ → x ._W⟶_.w-set _ _)
                                           (isProp× (isPropΠ λ _ → x ._W⟶_.w-set _ _)
                                           (isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → x ._W⟶_.w-set _ _))))))
                (cong₂ _,_ (funExt (λ w → funExt (p w))) (cong₂ _,_ (funExt (λ w → funExt (q w))) r))) 
              ; sigma-iso .leftInv y
open W⟶-Eq using (W⟶-≡) public
