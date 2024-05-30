module Util.Scope where

open import Data.List
open import Data.List.Relation.Binary.Permutation.Propositional
open import Relation.Binary.Definitions using (_Respects_)
open import Relation.Nullary.Decidable.Core

-- Scope is defined as a list of names.
--
Scope : (name : Set) → Set
Scope name = List name

-- type \Phi to get Φ
Φ : {name : Set} → Scope name
Φ = []

-- An assertion for "x is a member of the scope".
-- 
data _∈_ {name : Set} (x : name) : Scope name → Set where
    -- type \in to get ∈
    here  : ∀ {ns : Scope name}                         → x ∈ (x ∷ ns)
    there : ∀ {n : name} {ns : Scope name} (_ : x ∈ ns) → x ∈ (n ∷ ns)

∈-resp-↭ : ∀ {name : Set} {x : name} → (x ∈_) Respects _↭_
∈-resp-↭ refl i = i
∈-resp-↭ (prep _ _) here = here
∈-resp-↭ (prep _ p) (there i) = there (∈-resp-↭ p i)
∈-resp-↭ (swap _ _ _) here = there here
∈-resp-↭ (swap _ _ _) (there here) = here
∈-resp-↭ (swap _ _ p) (there (there i)) = there (there (∈-resp-↭ p i))
∈-resp-↭ (trans p p₁) i = ∈-resp-↭ p₁ (∈-resp-↭ p i)
