module Everything where

open import Data.String

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
  ƛx⇒x = ƛ "x" ⇒ (` "x" # here)

  id0 : Term Φ
  id0 = ƛx⇒x · `zero

  ℕ⇒ℕ : Type
  ℕ⇒ℕ = `ℕ ⇒ `ℕ

  ⊢ƛx⇒x:ℕ⇒ℕ : Evaluator (∅ ⊢ ƛx⇒x :: ℕ⇒ℕ)
  ⊢ƛx⇒x:ℕ⇒ℕ = checkType ∅ ƛx⇒x ℕ⇒ℕ

  ⊢id0:ℕ : Evaluator (∅ ⊢ id0 :: `ℕ)
  ⊢id0:ℕ = checkType ∅ id0 `ℕ

  testid : ⊢ƛx⇒x:ℕ⇒ℕ ≡ return (⊢ƛ (⊢` here))
  testid = refl

  testid0 : ⊢id0:ℕ ≡ return (⊢· (⊢ƛ (⊢` here)) (⊢zero))
  testid0 = refl
