open import Relation.Binary using (DecidableEquality)

module TypeChecker {name : Set} (_≟_ : DecidableEquality name) where

open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Effect.Monad using (RawMonad)
open RawMonad ⦃ ... ⦄
open import Function.Base using (case_of_)

open import Term {name}
open import TypeChecker.Type {name}
open import Util.Evaluator
open import Util.Map _≟_

{-# TERMINATING #-}
_<:?_ : Type → Type → Evaluator ⊤
a <:? `⊤ = return tt
`ℕ <:? `ℕ = return tt
`ℕ <:? `ℤ = return tt
`ℤ <:? `ℤ = return tt
(a ⇒ b) <:? (c ⇒ d) = do
  _ ← c <:? a
  _ ← b <:? d
  return tt
(Rec r) <:? (Rec []) = return tt
(Rec r) <:? (Rec ((k , v) ∷ s)) = do
  w ← lookup k r
  _ ← w <:? v
  _ ← (Rec r) <:? (Rec s)
  return tt
a <:? b = evalError "incompatible types"

infer : Map Type → Term → Evaluator Type
check : Map Type → Term → Type → Evaluator ⊤

infer ctx (` x) = lookup x ctx
infer ctx (ƛ x :: ty ⇒ body) = do
  bt ← infer ((x , ty) ∷ ctx) body
  return (ty ⇒ bt)
infer ctx (lam · arg) = do
  (a ⇒ b) ← infer ctx lam
    where _ → evalError "cannot apply non-function"
  _ ← check ctx arg a
  return b
infer ctx (rec []) = return (Rec [])
infer ctx (rec ((k , v) ∷ c)) = do
  vt ← infer ctx v
  Rec r ← infer ctx (rec c)
    where _ → evalError "unreachable"
  case lookup k r of λ
    { (inj₂ _) → evalError "duplicate key"
    ; (inj₁ _) → return (Rec ((k , vt) ∷ r))
    }
infer ctx (get k r) = do
  Rec r ← infer ctx r
    where
      _ → evalError "cannot get from non-record"
  lookup k r
infer ctx `zero = return `ℕ
infer ctx (`suc n) = do
  `ℕ ← infer ctx n
    where
      _ → evalError "suc expects a natural"
  return `ℕ
infer ctx (`pos n) = do
  `ℕ ← infer ctx n
    where
      _ → evalError "pos expects a natural"
  return `ℤ
infer ctx (`negsuc n) = do
  `ℕ ← infer ctx n
    where
      _ → evalError "pos expects a natural"
  return `ℤ

check ctx term t = do
  s ← infer ctx term
  s <:? t
