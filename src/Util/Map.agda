open import Relation.Binary using (DecidableEquality)

module Util.Map {K V : Set} (_≟ₖ_ : DecidableEquality K) (_≟ᵥ_ : DecidableEquality V) where

open import Axiom.UniquenessOfIdentityProofs using (UIP; module Decidable⇒UIP)
open import Data.Bool using (true; false)
open import Data.List hiding (lookup)
open import Data.List.Relation.Unary.Any hiding (lookup)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.List.Relation.Unary.First using (First) renaming ([_] to [_]¹; _∷_ to _∷¹_)
open import Data.List.Relation.Unary.First.Properties using (cofirst?; irrelevant)
open import Function.Base using (_on_; _∘_; case_of_)
open import Level using (0ℓ; suc)
open import Relation.Binary as Binary using (Rel; _⇒_)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive; Decidable)
open import Relation.Binary.Bundles using (DecSetoid; Setoid)
open import Relation.Binary.Structures using (IsEquivalence; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_; Dec; does; yes; no; contradiction; Irrelevant)
open import Relation.Unary using (Pred; ∁)
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

_∈₁_ : KV → Map → Set
_∈₁_ e = Any (e ≡₁_)

_∈₁?_ : Decidable _∈₁_
(k , v) ∈₁? m = any? ((k ≟ₖ_) ∘ proj₁) m

_∈₁′_ : KV → Map → Set
_∈₁′_ k = First (k ≢₁_) (k ≡₁_)

_∈₁′?_ : Decidable _∈₁′_
_∈₁′?_ (k , v) = cofirst?  ((k ≟ₖ_) ∘ proj₁)

∈₁′-irrelevant : ∀ {x} {m} → Irrelevant (x ∈₁′ m)
∈₁′-irrelevant {k , v} =
  irrelevant (λ p q → contradiction q p) (∁-irrelevant ((k , v) ≡₁_ ) {_ , v}) (≡₁-irrelevant {x = k , v} {y = _ , v})

_⊆_ : Rel Map 0ℓ
a ⊆ b = All (_∈₁ b) a

_⊆′_ : Rel Map 0ℓ
a ⊆′ b = All (_∈₁′ b) a

_⊆?_ : Decidable _⊆_
a ⊆? b = all? (_∈₁? b) a

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

lookup₁ : ∀ {x} {m} → x ∈₁ m → V
lookup₁ {k , v} (here px) = v
lookup₁ {x} (there p) = lookup₁ {x = x} p

lookup₁′ : ∀ {x} {m} → x ∈₁′ m → V
lookup₁′ {k , v} ([ px ]¹) = v
lookup₁′ {x} (px ∷¹ p) = lookup₁′ {x} p

lookup : ∀ {k} {m} → k ∈ₖ m → V
lookup {m = (k , v) ∷ _} (here p) = v
lookup (there p) = lookup p

lookup′ : ∀ {k} {m} → k ∈ₖ′ m → V
lookup′ {m = x ∷ _} ([ qx ]¹) = proj₂ x
lookup′ (px ∷¹ xs) = lookup′ xs

∈ₖ′⇒∈′ : ∀ {k} {m} {v : V} (i : k ∈ₖ′ m) → v ≡ lookup′ i → (k , v) ∈′ m
∈ₖ′⇒∈′ [ refl ]¹ refl = [ refl ]¹
∈ₖ′⇒∈′ (x ∷¹ i) refl with ∈ₖ′⇒∈′ i refl
... | [ y ]¹ = (λ { refl → x refl }) ∷¹ [ y ]¹
... | y ∷¹ j = (λ { refl → x refl }) ∷¹ y ∷¹ j

∈′⇒∈ₖ′ : ∀ {k} {v} {m} → (k , v) ∈′ m → k ∈ₖ′ m
∈′⇒∈ₖ′ {k} {m = m} i with k ∈ₖ′? m
... | yes j = j
∈′⇒∈ₖ′ {k} {m = .((k , _) ∷ _)} [ refl ]¹ | no ¬j = contradiction [ refl ]¹ ¬j
∈′⇒∈ₖ′ {k} {m = (l , v) ∷ _} (¬eq ∷¹ i) | no ¬j with k ≟ₖ l
... | no ¬keq = contradiction ((λ { refl → contradiction refl ¬keq }) ∷¹ ∈′⇒∈ₖ′ i) ¬j
... | yes refl = contradiction [ refl ]¹ ¬j
