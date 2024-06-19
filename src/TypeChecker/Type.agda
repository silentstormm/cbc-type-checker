open import Relation.Binary using (DecidableEquality)

module TypeChecker.Type {name : Set} where

open import Data.List using (List)
open import Data.Product using (_×_)

data Type : Set where
  `⊤ : Type
  `ℕ : Type
  `ℤ : Type
  _⇒_ : (a b : Type) → Type
  Rec : List (name × Type) → Type -- not Map to avoid parameter 

infixr 4 _⇒_
