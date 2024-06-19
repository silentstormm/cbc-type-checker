module Util.Scope where

open import Data.List
open import Relation.Binary.Definitions using (_Respects_)
open import Relation.Nullary.Decidable.Core

-- Scope is defined as a list of names.
Scope : (name : Set) → Set
Scope name = List name

Φ : {name : Set} → Scope name
Φ = []

-- An assertion for "x is a member of the scope".
-- data _∈_ {name : Set} (x : name) : Scope name → Set where
--   here  : ∀ {ns : Scope name}                         → x ∈ (x ∷ ns)
--   there : ∀ {n : name} {ns : Scope name} (_ : x ∈ ns) → x ∈ (n ∷ ns)
