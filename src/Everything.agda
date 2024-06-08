module Everything where

open import Data.String
open import Data.Product
open import Relation.Nullary using (yes; no; contradiction; map′; Dec; does; proof; from-yes)

name = String

open import Term _≟_
open import TypeChecker _≟_
open import TypeChecker.Type _≟_
open import TypeChecker.TypingRules _≟_
open import Util.Context {name}
open import Util.Evaluator
open import Util.Scope

private
  open import Agda.Builtin.Equality

  open import Effect.Monad
  open RawMonad ⦃ ... ⦄

  ƛx⇒x : Term Φ
  ƛx⇒x = ƛ "x" :: `ℕ ⇒ (` "x" # here)

  id0 : Term Φ
  id0 = ƛx⇒x · `zero

  ℕ⇒ℕ : Type
  ℕ⇒ℕ = `ℕ ⇒ `ℕ

  ⊢ƛx⇒x:ℕ⇒ℕ : Evaluator (Σ[ s ∈ Type ] ((s <: ℕ⇒ℕ) × (∅ ⊢ ƛx⇒x :: s)))
  ⊢ƛx⇒x:ℕ⇒ℕ = checkType ∅ ƛx⇒x ℕ⇒ℕ

  ⊢id0:ℕ : Evaluator (Σ[ s ∈ Type ] ((s <: `ℕ) × ∅ ⊢ id0 :: s))
  ⊢id0:ℕ = checkType ∅ id0 `ℕ

  itestid : (inferType ∅ ƛx⇒x) ≡ return (ℕ⇒ℕ , ⊢ƛ (⊢` here))
  itestid = refl

  subtestid : (ℕ⇒ℕ <:? ℕ⇒ℕ) ≡ (yes (<:⇒ <:ℕ <:ℕ))
  subtestid with ℕ⇒ℕ <:? ℕ⇒ℕ
  ... | yes (<:⇒ <:ℕ <:ℕ) = refl
  ... | no ¬sub = contradiction (<:⇒ <:ℕ <:ℕ) ¬sub

  testid : ⊢ƛx⇒x:ℕ⇒ℕ ≡ return (ℕ⇒ℕ , <:⇒ <:ℕ <:ℕ , ⊢ƛ (⊢` here))
  testid rewrite subtestid = refl

  -- testid0 : ⊢id0:ℕ ≡ return (⊢· (⊢ƛ (⊢` here)) (⊢zero))
  -- testid0 = ?
