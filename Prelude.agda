{-# OPTIONS --safe #-}

module Prelude where

open import Data.Sigma public
open import Data.Empty public
open import Data.Unit public
open import Data.Bool public
open import Data.Nat public
open import Data.Fin public
open import Data.Maybe public
open import Level public
open import Level.Literals public
open import Function public
open import Path public
open import Data.Sum public
open import Isomorphism public
open import Data.List public
open import HLevels public
open import Decidable public
open import Discrete public
open import Discrete.IsSet public
open import Inspect public
-- open import Literals.Number public
open import Identity public
open import Data.Bool.Properties public
open import Strict public
open import Data.Lift public
open import Also public

open import Data.Unit.UniversePolymorphic
  renaming (⊤ to Poly-⊤; tt to Poly-tt)
  public

open import Data.Empty.UniversePolymorphic
  renaming (⊥ to Poly-⊥)
  public
open import Data.Empty.Properties
  using (isProp⊥)
  public

open import HITs.SetQuotients public
open import HITs.PropositionalTruncation public

open import Data.Sigma.Properties public

open import WellFounded public
open import Path.Reasoning public
