open import Relation.Binary using (DecidableEquality; Rel)

module TypeChecker.Type {name : Set} (_≟_ : DecidableEquality name) where

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

open import Util.Context {name}
open import Util.Map _≟_
open import Util.Scope

data Type : Set where
  `⊤ : Type
  `ℕ : Type
  `ℤ : Type
  _⇒_ : (a b : Type) → Type
  Rec : Map Type → Type

infixr 4 _⇒_
