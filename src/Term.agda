open import Relation.Binary using (DecidableEquality)

module Term {name : Set} (_≟_ : DecidableEquality name) where

open import Data.List

open import Util.Context {name}
open import Util.Map _≟_ using (Map)
open import Util.Scope

private variable
  α : Scope name

data Term (α : Scope name) : Set where
  `_#_ : (x : name) → x ∈ α → Term α
  ƛ_⇒_ : (x : name) (v : Term (x ∷ α)) → Term α
  _·_   : (u v : Term α) → Term α
  rec : Map (Term α) → Term α
  get : (k : name) → (r : Term α) → Term α
  `zero : Term α
  `suc : Term α → Term α
  `pos : Term α → Term α
  `negsuc : Term α → Term α

infix  5  ƛ_⇒_
infixl 7  _·_
infix  9  `_#_
