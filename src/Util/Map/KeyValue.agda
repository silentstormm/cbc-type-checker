open import Relation.Binary using (DecidableEquality)

module Util.Map.KeyValue {K V : Set} (_≟ₖ_ : DecidableEquality K) (_≟ᵥ_ : DecidableEquality V) where

open import Data.Product using (_×_)
open import Data.Product.Properties using (≡-dec)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; Irrelevant; yes; no)

open import Data.Product using (_,_; proj₁; proj₂) public

KV : Set
KV = K × V

_≟_ : DecidableEquality KV
a ≟ b = ≡-dec _≟ₖ_ _≟ᵥ_ a b

_≡₁_ : KV → KV → Set
_≡₁_ = (_∘ proj₁) ∘ _≡_ ∘ proj₁

≡₁-irrelevant : ∀ {x y : KV} → Irrelevant (x ≡₁ y)
≡₁-irrelevant refl refl = refl

_≢₁_ : KV → KV → Set
x ≢₁ y = ¬ x ≡₁ y

_≡ₖ_ : K → KV → Set
_≡ₖ_ = (_∘ proj₁) ∘ _≡_

≡ₖ-irrelevant : ∀ {k l} {v : V} → Irrelevant (k ≡ₖ (l , v))
≡ₖ-irrelevant refl refl = refl

_≢ₖ_ : K → K × V → Set
x ≢ₖ y = ¬ x ≡ₖ y
