open import Relation.Binary using (DecidableEquality)

module TypeChecker.TypingRules {name : Set} (_≟ₙ_ : DecidableEquality name) where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.First as First using ([_]; _∷_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Function.Base using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; sym)
open import Relation.Nullary as N using (yes; no; contradiction)
open import Relation.Nullary.Negation using (¬_)

open import Term
open import Term.Properties _≟ₙ_ renaming (_≟_ to _≟ᵤ_)
open import TypeChecker.Type {name}
open import TypeChecker.Type.Properties _≟ₙ_ renaming (_≟_ to _≟ₜ_)
open import Util.Map _≟ₙ_ _≟ₜ_
open import Util.Map _≟ₙ_ _≟ᵤ_ as Record using () renaming (Map to Record)

private variable
  x : name
  A B C D : Type
  u v : Term

data _<:_ : Rel Type 0ℓ where
  <:⊤
    : A <: `⊤

  <:⇒
    : C <: A
    → B <: D
    ---------------------------------
    → A ⇒ B <: C ⇒ D

  <:ℕ
    : `ℕ <: `ℕ

  <:ℤ
    : `ℤ <: `ℤ

  ℕ<:ℤ
    ---------------------------------
    : `ℕ <: `ℤ

  <:rec
    : {m n : Map}
    → n ⊆′ m
    → All (λ { (k , v) → (i : k ∈ₖ′ m) → lookup′ i <: v}) n
    ---------------------------------
    → Rec m <: Rec n
infix 3 _<:_

{-# TERMINATING #-}
_<:?_ : Decidable _<:_
s <:? `⊤ = yes <:⊤
`⊤ <:? `ℕ = no (λ ())
`ℕ <:? `ℕ = yes <:ℕ
`ℤ <:? `ℕ = no (λ ())
(sa ⇒ sb) <:? `ℕ = no (λ ())
Rec x <:? `ℕ = no (λ ())
`⊤ <:? `ℤ = no (λ ())
`ℕ <:? `ℤ = yes ℕ<:ℤ
`ℤ <:? `ℤ = yes <:ℤ
(s ⇒ s₁) <:? `ℤ = no (λ ())
Rec x <:? `ℤ = no (λ ())
`⊤ <:? (ta ⇒ tb) = no (λ ())
`ℕ <:? (ta ⇒ tb) = no (λ ())
`ℤ <:? (ta ⇒ tb) = no (λ ())
(sa ⇒ sb) <:? (ta ⇒ tb) with ta <:? sa
... | no ¬a = no λ { (<:⇒ a _) → contradiction a ¬a }
... | yes a with sb <:? tb
... | yes b = yes (<:⇒ a b)
... | no ¬b = no λ { (<:⇒ _ b) → contradiction b ¬b }
Rec x <:? (ta ⇒ tb) = no (λ ())
`⊤ <:? Rec x = no (λ ())
`ℕ <:? Rec x = no (λ ())
`ℤ <:? Rec x = no (λ ())
(sa ⇒ sb) <:? Rec x = no (λ ())
--Rec m <:? Rec [] = {!!}
--Rec m <:? Rec (x ∷ n) = {!!}
Rec m <:? Rec n with n ⊆′? m
... | no ¬s = no λ { (<:rec s _) → contradiction s ¬s }
(Rec m <:? Rec []) | yes subset = yes (<:rec subset All.[])
(Rec m <:? Rec ((k , v) ∷ o)) | yes subset with k ∈ₖ′? m
... | no i = contradiction (All.head subset) i
... | yes i with lookup′ i <:? v
... | no subtype = no λ { (<:rec _ s) → contradiction s (λ { (px All.∷ f) → contradiction (px i) subtype })}
... | yes subtype with Rec m <:? Rec o
... | yes (<:rec s t) = yes (<:rec subset ((λ { j → lemma (∈ₖ′-irrelevant {v = v} i j) subtype }) All.∷ t))
  where
    lemma : ∀ {m : Map} {i j : x ∈ₖ′ m} → i ≡ j → lookup′ i <: A → lookup′ j <: A
    lemma refl s = s
... | no m<:o = no (m<:o ∘ λ { (<:rec (px All.∷ s) (px₁ All.∷ t)) → <:rec s t })

data _⊢_::_ (Γ : Map) : Term → Type → Set where
  ⊢`
    : (p : (x , A) ∈′ Γ) (q : x ∈ₖ′ Γ)
    → A ≡ lookup′ q
    ---------------------------------
    → Γ ⊢ ` x :: A

  ⊢ƛ
    : (x , A) ∷ Γ ⊢ u :: B
    ---------------------------------
    → Γ ⊢ (ƛ x :: A ⇒ u) :: A ⇒ B

  ⊢·
    : Γ ⊢ u :: (A ⇒ B)
    → Γ ⊢ v :: C
    → C <: A
    ---------------------------------
    → Γ ⊢ u · v :: B

  ⊢rec-empty
    ---------------------------------
    : Γ ⊢ rec [] :: Rec []

  ⊢rec-more
    : {rs : Record} {rt : Map}
    → ¬ (x ∈ₖ′ rt)
    → Γ ⊢ rec rs :: Rec rt
    → Γ ⊢ v :: A
    ---------------------------------
    → Γ ⊢ rec ((x , v) ∷ rs) :: Rec ((x , A) ∷ rt)

  ⊢get
    : {r : Map} (p : (x , A) ∈′ r) (q : x ∈ₖ′ r)
    → A ≡ lookup′ q
    → Γ ⊢ v :: Rec r
    ---------------------------------
    → Γ ⊢ get x v :: A

  ⊢zero
    ---------------------------------
    : Γ ⊢ `zero :: `ℕ

  ⊢suc
    : Γ ⊢ v :: `ℕ
    ---------------------------------
    → Γ ⊢ `suc v :: `ℕ

  ⊢pos
    : Γ ⊢ v :: `ℕ
    ---------------------------------
    → Γ ⊢ `pos v :: `ℤ

  ⊢negsuc
    : Γ ⊢ v :: `ℕ
    ---------------------------------
    → Γ ⊢ `negsuc v :: `ℤ

infix 3 _⊢_::_

getType : ∀ {Γ : Map} → Γ ⊢ v :: A → Σ[ t ∈ Type ] t ≡ A
getType {Γ = Γ} (⊢` {x} {A = A} _ _ _) = A , refl
getType (⊢ƛ {A = A} {B = B} _) = (A ⇒ B) , refl
getType (⊢· {B = B} _ _ _) = B , refl
getType ⊢rec-empty = Rec [] , refl
getType (⊢rec-more {x = x} {A = A} {rt = rt} _ _ _) = (Rec ((x , A) ∷ rt)) , refl
getType (⊢get {A = A} _ _ _ _) = A , refl
getType ⊢zero = `ℕ , refl
getType (⊢suc _) = `ℕ , refl
getType (⊢pos _) = `ℤ , refl
getType (⊢negsuc _) = `ℤ , refl

private
  fun-lemma : (A ⇒ B) ≡ (C ⇒ D) → B ≡ D
  fun-lemma refl = refl

  rec-lemma : ∀ {r s} → Rec r ≡ Rec s → r ≡ s
  rec-lemma refl = refl

⊢type-irrelevant : ∀ {Γ} → Γ ⊢ v :: A → Γ ⊢ v :: B → A ≡ B
⊢type-irrelevant (⊢` {A = A} p q refl) (⊢` r s refl) rewrite ∈ₖ′-irrelevant {v = A} q s = refl
⊢type-irrelevant (⊢ƛ {A = A} a) (⊢ƛ b) rewrite ⊢type-irrelevant a b = refl
⊢type-irrelevant (⊢· l a s) (⊢· m b t) rewrite fun-lemma (⊢type-irrelevant l m) = refl
⊢type-irrelevant ⊢rec-empty ⊢rec-empty = refl
⊢type-irrelevant (⊢rec-more p ra va) (⊢rec-more q rb vb) rewrite rec-lemma (⊢type-irrelevant ra rb) | ⊢type-irrelevant va vb = refl
⊢type-irrelevant (⊢get pa qa refl a) (⊢get {A = B} pb qb refl b) rewrite rec-lemma (⊢type-irrelevant a b) | ∈ₖ′-irrelevant {v = B} qa qb = refl
⊢type-irrelevant ⊢zero ⊢zero = refl
⊢type-irrelevant (⊢suc a) (⊢suc b) = refl
⊢type-irrelevant (⊢pos a) (⊢pos b) = refl
⊢type-irrelevant (⊢negsuc a) (⊢negsuc b) = refl
