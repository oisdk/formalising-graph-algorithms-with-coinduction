{-# OPTIONS --safe #-}

module Finite where

open import Prelude
open import Data.Set renaming (_∈_ to _𝒦∈_; _∉_ to _𝒦∉_)
open import Data.List.Properties

Finite : Type a → Type a
Finite A = Σ[ supp ⦂ List A ] × (∀ x → x ∈ supp)

data NoethAcc {A : Type a} (seen : 𝒦 A) : Type a where
  nacc : (∀ x → x 𝒦∉ seen → NoethAcc (x ∷ seen)) → NoethAcc seen

module NoethFinite (fin : Finite A) where
  supp = fst fin
  cover = snd fin

  Finite→Discrete : Discrete A
  Finite→Discrete x y with cover x | inspect cover x | cover y | inspect cover y
  ... | i , cx | 〖 ri 〗 | j , cy | 〖 rj 〗 with discreteFin i j
  ... | yes i≡j = yes (sym cx ; cong (supp !!_) i≡j ; cy)
  ... | no  i≢j = no λ x≡y → i≢j (sym (cong fst ri) ; cong (fst ∘′ snd fin) x≡y ; cong fst rj)

  open import Data.Set.Discrete Finite→Discrete
  import Data.Set.Noetherian Finite→Discrete as NA

  opaque
    noetherian : NoethAcc {A = A} ∅
    noetherian = go (NA.noeth (𝒦-fromList supp))
      where
      go : ∀ {seen} → NA.NoethAcc (𝒦-fromList supp) seen → NoethAcc seen
      go (NA.nacc wf) = nacc λ x x∉seen → go (wf x (∈-fromList x supp (cover x)) x∉seen)
