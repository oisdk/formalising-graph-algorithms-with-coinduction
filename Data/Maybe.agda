{-# OPTIONS --safe #-}

module Data.Maybe where

open import Level
open import Agda.Builtin.Maybe public

maybe′ : {B : Maybe A → Type b} → B nothing → ((x : A) → B (just x)) → (x : Maybe A) → B x
maybe′ b f nothing = b
maybe′ b f (just x) = f x
{-# INLINE maybe′ #-}

maybe : B → (A → B) → Maybe A → B
maybe = maybe′
{-# INLINE maybe #-}

map-maybe : (A → B) → Maybe A → Maybe B
map-maybe f nothing  = nothing
map-maybe f (just x) = just (f x)

from-maybe : A → Maybe A → A
from-maybe x mx = maybe x (λ x → x) mx
{-# INLINE from-maybe #-}

infixr 4.3 _??_
_??_ : Maybe A → A → A
xs ?? x = from-maybe x xs

open import Data.Bool

guard : Bool → A → Maybe A
guard b x = bool′ nothing (just x) b

ensure : (A → Bool) → A → Maybe A
ensure p x = guard (p x) x
