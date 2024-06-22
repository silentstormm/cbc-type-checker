open import Relation.Binary using (DecidableEquality)

module Util.Map {K V : Set} (_≟ₖ_ : DecidableEquality K) (_≟ᵥ_ : DecidableEquality V) where

open import Axiom.UniquenessOfIdentityProofs using (UIP; module Decidable⇒UIP)
open import Data.List hiding (lookup)
open import Data.List.Relation.Unary.Any hiding (lookup)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.List.Relation.Unary.First as F using (First)
open import Data.List.Relation.Unary.First.Properties using (cofirst?; irrelevant)
open import Function.Base using (_∘_; case_of_)
open import Level using (0ℓ)
open import Relation.Binary as Binary using (Rel)
open import Relation.Binary.Definitions using (Reflexive; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no; contradiction; Irrelevant)
open import Relation.Unary.Properties using (∁-irrelevant)

open import Util.Map.KeyValue _≟ₖ_ _≟ᵥ_

Map : Set
Map = List KV

_∈′_ : KV → Map → Set
_∈′_ x = First (x ≢_) (x ≡_)

_∈′?_ : Decidable _∈′_
_∈′?_ x = cofirst?  (x ≟_)

∈′-irrelevant : ∀ {x} {m : Map} → Irrelevant (x ∈′ m)
∈′-irrelevant {x} {m} = irrelevant (λ p q → contradiction q p) (∁-irrelevant (x ≡_)) (Decidable⇒UIP.≡-irrelevant _≟_)

_∈ₖ_ : K → Map → Set
_∈ₖ_ k = Any (k ≡ₖ_)

_∈ₖ?_ : Decidable _∈ₖ_
k ∈ₖ? m = any? ((k ≟ₖ_) ∘ proj₁) m

_∈ₖ′_ : K → Map → Set
_∈ₖ′_ k = First (k ≢ₖ_) (k ≡ₖ_)

_∈ₖ′?_ : Decidable _∈ₖ′_
_∈ₖ′?_ k = cofirst?  ((k ≟ₖ_) ∘ proj₁)

∈ₖ′-irrelevant : ∀ {v : V} {k} {m} → Irrelevant (k ∈ₖ′ m)
∈ₖ′-irrelevant {v} {k} = irrelevant (λ p q → contradiction q p) (∁-irrelevant (k ≡ₖ_) {_ , v}) (≡ₖ-irrelevant {v = v})

_∈₁′_ : KV → Map → Set
_∈₁′_ k = First (k ≢₁_) (k ≡₁_)

_∈₁′?_ : Decidable _∈₁′_
_∈₁′?_ (k , v) = cofirst?  ((k ≟ₖ_) ∘ proj₁)

∈₁′-irrelevant : ∀ {x} {m} → Irrelevant (x ∈₁′ m)
∈₁′-irrelevant {k , v} =
  irrelevant (λ p q → contradiction q p) (∁-irrelevant ((k , v) ≡₁_ ) {_ , v}) (≡₁-irrelevant {x = k , v} {y = _ , v})

_⊆′_ : Rel Map 0ℓ
a ⊆′ b = All (_∈₁′ b) a

_⊆′?_ : Decidable _⊆′_
a ⊆′? b = all? (_∈₁′? b) a

⊆′-irrelevant : Binary.Irrelevant _⊆′_
⊆′-irrelevant All.[] All.[] = refl
⊆′-irrelevant (All._∷_ {x = k , v} px a) (qx All.∷ b) rewrite ∈₁′-irrelevant {_ , v} px qx | ⊆′-irrelevant a b = refl

⊆′-refl : Reflexive  _⊆′_
⊆′-refl {[]} = All.[]
⊆′-refl {(k , v) ∷ xs} = First.[ refl ] All.∷ (All.map (λ { {l , w} i → case l ≟ₖ k of λ
  { (no ¬eq) → ¬eq First.∷ i
  ; (yes refl) → First.[ refl ]
  } }) (⊆′-refl {xs}))

lookup₁′ : ∀ {x} {m} → x ∈₁′ m → V
lookup₁′ {k , v} (F.[ px ]) = v
lookup₁′ {x} (px F.∷ p) = lookup₁′ {x} p

lookup′ : ∀ {k} {m} → k ∈ₖ′ m → V
lookup′ {m = x ∷ _} (F.[ qx ]) = proj₂ x
lookup′ (px F.∷ xs) = lookup′ xs

∈ₖ′⇒∈′ : ∀ {k} {m} {v : V} (i : k ∈ₖ′ m) → v ≡ lookup′ i → (k , v) ∈′ m
∈ₖ′⇒∈′ F.[ refl ] refl = F.[ refl ]
∈ₖ′⇒∈′ (x F.∷ i) refl with ∈ₖ′⇒∈′ i refl
... | F.[ y ] = (λ { refl → x refl }) F.∷ F.[ y ]
... | y F.∷ j = (λ { refl → x refl }) F.∷ y F.∷ j
