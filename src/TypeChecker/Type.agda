module TypeChecker.Type {name : Set} where

open import Util.Context {name}
open import Util.Scope

data Type : Set where
  `ℕ : Type
  _⇒_ : (a b : Type) → Type
  Rec : {β : Scope name} → (l : Context Type β) → Type
