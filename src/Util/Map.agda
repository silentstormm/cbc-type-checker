open import Relation.Binary using (DecidableEquality)

module Util.Map {K : Set} (_≟_ : DecidableEquality K) where

open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Effect.Monad using (RawMonad)
open RawMonad ⦃ ... ⦄
open import Relation.Nullary using (yes; no)

open import Util.Evaluator

Map : Set → Set
Map V = List (K × V)

lookup : ∀ {V} → K → Map V → Evaluator V
lookup l [] = evalError "nonexistent key"
lookup k ((l , v) ∷ m) with k ≟ l
... | no _ = lookup k m
... | yes _ = return v

_⊆?_ : ∀ {V} → Map V → Map V → Evaluator ⊤
[] ⊆? b = return tt
((k , _) ∷ a) ⊆? b = do
  _ ← lookup k b
  a ⊆? b
