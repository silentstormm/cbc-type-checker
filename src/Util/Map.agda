open import Relation.Binary using (DecidableEquality)

module Util.Map {name : Set} (_≟_ : DecidableEquality name) where

open import Data.Bool using (true; false)
open import Data.List hiding (lookup)
open import Data.List.Relation.Unary.Any hiding (lookup)
open import Data.List.Relation.Unary.All using (All; all?)
open import Data.List.Relation.Unary.First using (First) renaming ([_] to [_]¹; _∷_ to _∷¹_)
open import Data.List.Relation.Unary.First.Properties using (cofirst?; irrelevant)
open import Data.Product
open import Function.Base using (_on_; _∘_)
open import Level using (0ℓ; suc)
open import Relation.Binary using (Rel; _⇒_)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive; Decidable)
open import Relation.Binary.Bundles using (DecSetoid; Setoid)
open import Relation.Binary.Structures using (IsEquivalence; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; does; yes; no; contradiction; Irrelevant)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Unary using (Pred; ∁)
open import Relation.Unary.Properties using (∁-irrelevant)

private variable
  V : Set

data _≟₁_ (l : name × V) : name × V → Set where
  refl₁ : ∀ {w : V} → (proj₁ l , proj₂ l) ≟₁ (proj₁ l , w)

≟₁-refl : ∀ {V} → Reflexive (_≟₁_ {V})
≟₁-refl = refl₁

≟₁-sym : ∀ {V} → Symmetric (_≟₁_ {V})
≟₁-sym refl₁ = refl₁

≟₁-trans : ∀ {V} → Transitive (_≟₁_ {V})
≟₁-trans refl₁ refl₁ = refl₁

≟₁-≟ : ∀ {V} → Decidable (_≟₁_ {V})
≟₁-≟ (fst , snd) (fst₁ , snd₁) with fst ≟ fst₁
... | yes refl = yes refl₁
... | no ¬proof = no (¬proof ∘ ≟₁-pre)
  where
    ≟₁-pre : (x : (fst , snd) ≟₁ (fst₁ , snd₁)) → fst ≡ fst₁
    ≟₁-pre refl₁ = refl

Quotient : (S : Set) (_∼_ : Rel S 0ℓ) (ER : IsDecEquivalence _∼_) → DecSetoid _ _
Quotient S _~_ ER = record
  { Carrier = S
  ; _≈_ = _~_
  ; isDecEquivalence = ER
  }

KeyEquiv : (V : Set) →  DecSetoid _ _
KeyEquiv V = Quotient (name × V) _≟₁_ ≟₁-isDec
  where
    ≟₁-isEQ : IsEquivalence _≟₁_
    ≟₁-isEQ = record
      { refl = ≟₁-refl
      ; sym = ≟₁-sym
      ; trans = ≟₁-trans
      }
    ≟₁-isDec : IsDecEquivalence _≟₁_
    ≟₁-isDec = record
      { isEquivalence = ≟₁-isEQ
      ; _≟_ = ≟₁-≟
      }

Map : (V : Set) → Set
Map V = List (name × V)

_≡₁_ : name × V → name × V → Set
_≡₁_ = (_∘ proj₁) ∘ _≡_ ∘ proj₁

_≢₁_ : name × V → name × V → Set
x ≢₁ y = ¬ x ≡₁ y

_≡ₖ_ : name → name × V → Set
_≡ₖ_ = (_∘ proj₁) ∘ _≡_

≡ₖ-irrelevant : ∀ {k l} {v : V} → Irrelevant (k ≡ₖ (l , v))
≡ₖ-irrelevant refl refl = refl

_≢ₖ_ : name → name × V → Set
x ≢ₖ y = ¬ x ≡ₖ y

_∈ₖ_ : name → Map V → Set
_∈ₖ_ k = Any (k ≡ₖ_)

_∈ₖ?_ : Decidable (_∈ₖ_ {V})
k ∈ₖ? m = any? ((k ≟_) ∘ proj₁) m

_∈ₖ′_ : name → Map V → Set
_∈ₖ′_ k = First (k ≢ₖ_) (k ≡ₖ_)

_∈ₖ′?_ : Decidable (_∈ₖ′_ {V})
_∈ₖ′?_ k = cofirst?  ((k ≟_) ∘ proj₁)

∈ₖ′-irrelevant : {v : V} → ∀ {k} {m : Map V} → Irrelevant (k ∈ₖ′ m)
∈ₖ′-irrelevant {V} {v} {k} =
  irrelevant (λ p q → contradiction q p) (∁-irrelevant (_≡ₖ_ {V} k) {_ , v}) (≡ₖ-irrelevant {V} {_} {_} {v})

_∈₁_ : name × V → Map V → Set
_∈₁_ e = Any (e ≡₁_)

_∈₁?_ : Decidable (_∈₁_ {V})
e ∈₁? m = any? ((proj₁ e ≟_) ∘ proj₁) m

_∈₁′_ : name × V → Map V → Set
_∈₁′_ k = First (k ≢₁_) (k ≡₁_)

_∈₁′?_ : Decidable (_∈₁′_ {V})
_∈₁′?_ k = cofirst?  ((proj₁ k ≟_) ∘ proj₁)

_⊆_ : Rel (Map V) 0ℓ
a ⊆ b = All (_∈₁ b) a

_⊆′_ : Rel (Map V) 0ℓ
a ⊆′ b = All (_∈₁′ b) a

--⊆-refl : Reflexive (_⊆_ {V})
--⊆-refl = {!!}

-- _⊆_ : Rel (Map V) 0ℓ
-- xs ⊆ ys = ∀ {x} → x ∈₁ xs → x ∈₁ ys

-- open import Relation.Nullary using (contradiction; map′; _×-dec_)

-- ⊆-∷ : ∀ {x} {a b} (i : x ∈₁ b) (y : a ⊆ b) → (x ∷ a) ⊆ b
-- ⊆-∷ {x} i s ai = {!!}

-- s2? : Decidable (_⊆_ {V})
-- s2? [] b = yes λ ()
-- s2? (x ∷ a) b = map′ (uncurry {!!}) {!!} ((x ∈₁? b) ×-dec s2? a b)
-- s2? (x ∷ a) b with x ∈₁? b
-- ... | yes p = {!s2? a (removeAt b (index p))!}
-- ... | no p with x ∈₁? (x ∷ a)
-- ... | yes i = no (p ∘ λ f → f {x} i)
-- ... | no i = contradiction (here refl) i

_⊆?_ : Decidable (_⊆_ {V})
a ⊆? b = all? (_∈₁? b) a

_⊆′?_ : Decidable (_⊆′_ {V})
a ⊆′? b = all? (_∈₁′? b) a

lookup : {k : name} {m : Map V} → k ∈ₖ m → V
lookup {m = x ∷ _} (here p) = proj₂ x
lookup (there p) = lookup p

lookup′ : {k : name} {m : Map V} → k ∈ₖ′ m → V
lookup′ {m = x ∷ _} ([ qx ]¹) = proj₂ x
lookup′ (px ∷¹ xs) = lookup′ xs
