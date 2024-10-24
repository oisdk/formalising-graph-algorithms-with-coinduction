{-# OPTIONS --safe #-}

module Isomorphism where

open import Cubical.Foundations.Isomorphism
  using (section; retract; isoToPath; iso; isoToEquiv)
  renaming (Iso to infix 4 _⇔_; compIso to trans-⇔; invIso to sym-⇔; idIso to id-⇔)
  public

open _⇔_ public
