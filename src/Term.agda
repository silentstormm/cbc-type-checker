module Term {name : Set} where

open import Data.List using (List)
open import Data.Product using (_×_)

open import TypeChecker.Type {name}

data Term : Set where
  `_ : name → Term
  ƛ_::_⇒_ : name → Type → Term → Term
  _·_   : (f a : Term) → Term
  rec : List (name × Term) → Term
  get : name → Term → Term
  `zero : Term
  `suc : Term → Term
  `pos : Term → Term
  `negsuc : Term → Term

infix  5  ƛ_::_⇒_
infixl 7  _·_
infix  9  `_
