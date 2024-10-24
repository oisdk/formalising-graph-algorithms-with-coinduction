{-# OPTIONS --safe #-}

module HLevels where

open import Cubical.Foundations.HLevels using
  (isSetΠ; isProp→; isSet×; isPropΠ; isPropΣ; isSetΣ; isOfHLevel→isOfHLevelDep)
  public
open import Cubical.Foundations.Everything using
  (isProp; isSet; isOfHLevel; isProp→isSet)
  public
