module Everything where

open import Data.List using ([])
open import Data.List.Relation.Unary.First
open import Data.Product
open import Data.String
open import Relation.Nullary using (yes; no; contradiction; map′; Dec; does; proof; from-yes)

name = String

open import Term {name}
open import TypeChecker _≟_
open import TypeChecker.Type {name}
open import TypeChecker.TypingRules _≟_
open import Util.Context {name}
open import Util.Evaluator
open import Util.Scope

private
  open import Agda.Builtin.Equality

  open import Effect.Monad
  open RawMonad ⦃ ... ⦄

  ƛx⇒x : Term
  ƛx⇒x = ƛ "x" :: `ℕ ⇒ (` "x")

  id0 : Term
  id0 = ƛx⇒x · `zero

  ℕ⇒ℕ : Type
  ℕ⇒ℕ = `ℕ ⇒ `ℕ

  ⊢ƛx⇒x:ℕ⇒ℕ : Dec (Σ[ s ∈ Type ] ((s <: ℕ⇒ℕ) × ([] ⊢ ƛx⇒x :: s)))
  ⊢ƛx⇒x:ℕ⇒ℕ = check? [] ƛx⇒x ℕ⇒ℕ

  ⊢id0:ℕ : Dec (Σ[ s ∈ Type ] ((s <: `ℕ) × [] ⊢ id0 :: s))
  ⊢id0:ℕ = check? [] id0 `ℕ

  itestid : (infer? [] ƛx⇒x) ≡ yes (ℕ⇒ℕ , ⊢ƛ (⊢` ([ refl ]) ([ refl ]) refl))
  itestid = refl

  subtestid : (ℕ⇒ℕ <:? ℕ⇒ℕ) ≡ (yes (<:⇒ <:ℕ <:ℕ))
  subtestid = refl

  testid : ⊢ƛx⇒x:ℕ⇒ℕ ≡ yes (ℕ⇒ℕ , <:⇒ <:ℕ <:ℕ , ⊢ƛ (⊢` [ refl ] [ refl ] refl))
  testid = refl

  testid0 : ⊢id0:ℕ ≡ yes (`ℕ , <:ℕ , (⊢· (⊢ƛ (⊢` [ refl ] [ refl ] refl)) ⊢zero <:ℕ))
  testid0 = refl
