module Everything where

open import Data.List using ([])
open import Data.Product
open import Data.String
open import Data.Unit using (⊤; tt)

name = String

open import Term {name}
open import TypeChecker _≟_
open import TypeChecker.Type {name}
open import Util.Evaluator

private
  open import Agda.Builtin.Equality

  open import Effect.Monad
  open RawMonad ⦃ ... ⦄

  ƛx⇒x : Term
  ƛx⇒x = ƛ "x" :: `⊤ ⇒ (` "x")

  id0 : Term
  id0 = ƛx⇒x · `zero

  ⊤⇒⊤ : Type
  ⊤⇒⊤ = `⊤ ⇒ `⊤

  ⊢ƛx⇒x:⊤⇒⊤ : Evaluator ⊤
  ⊢ƛx⇒x:⊤⇒⊤ = check [] ƛx⇒x ⊤⇒⊤

  ⊢id0:⊤ : Evaluator ⊤
  ⊢id0:⊤ = check [] id0 `⊤

  itestid : (infer [] ƛx⇒x) ≡ return ⊤⇒⊤
  itestid = refl

  subtestid : (⊤⇒⊤ <:? ⊤⇒⊤) ≡ return tt
  subtestid = refl

  testid : ⊢ƛx⇒x:⊤⇒⊤ ≡ return tt
  testid = refl

  testid0 : ⊢id0:⊤ ≡ return tt
  testid0 = refl
