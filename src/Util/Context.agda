module Util.Context {name : Set} where

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Util.Scope

private variable
  α : Scope name
  V : Set

Context : (V : Set) → (α : Scope name) → Set
Context V α = All (λ _ → V) α

∅ : Context V Φ
∅ = []

_,_::_ : Context V α → (x : name) → V → Context V (x ∷ α)
_,_::_ ctx _ v = v ∷ ctx
infix 4 _,_::_

lookupVar : (Γ : Context V α) (x : name) (p : x ∈ α) → V
lookupVar (v ∷ _  ) x (here _) = v
lookupVar (_ ∷ ctx) x (there p) = lookupVar ctx x p

data _::_∈_ (k : name) (v : V) : Context V α → Set where
  here  : ∀ {ns} {Δ : Context V (k ∷ ns)} → k :: v ∈ (_∷_ {x = k} v Δ)
  there : ∀ {n} {w} {ns} {Δ : Context V (n ∷ ns)} (_ : k :: v ∈ Δ) → k :: v ∈ (_∷_ {x = k} w Δ) -- Value and its evil twin Walue

-- aaaa : {k : name} (Γ : Context V α) (p : k ∈ α) (v : lookupVar Γ k p) → k :: v ∈ Γ
-- aaaa (px ∷ Γ) here _ = {!here!}
-- aaaa (px ∷ Γ) (there p) _ = {!!}
