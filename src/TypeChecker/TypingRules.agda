open import Relation.Binary using (DecidableEquality)

module TypeChecker.TypingRules {name : Set} (_≟_ : DecidableEquality name) where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional
-- open import Data.List.Relation.Binary.Sublist.Propositional
open import Data.List.Relation.Unary.First as First using ([_]; _∷_)
open import Data.List.Relation.Unary.All as All using (All) renaming (_∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.All.Properties using (Any¬⇒¬All)
open import Data.List.Relation.Unary.Any using (Any; here)
open import Data.Product
open import Function.Base using (_on_; _∘_; case_of_)
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel) renaming (_⇒_ to _=>_)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; inspect)
open import Relation.Nullary using (yes; no; contradiction; map′; Dec; does; proof; from-yes)
open import Relation.Nullary.Negation using (¬_)

open import Term _≟_
open import TypeChecker.Type _≟_
open import Util.Context {name}
open import Util.Map _≟_
open import Util.Scope

private variable
  x : name
  α β : Scope name
  A B C D : Type
  u v : Term α

data _<:_ : Rel Type 0ℓ where
  -- <:refl
  --   ---------------------------------
  --   : A <: A

  -- <:trans
  --   : A <: B
  --   → B <: C
  --   ---------------------------------
  --   → A <: C

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

  -- <:rec-empty
  --   : ∀ {m}
  --   ---------------------------------
  --   → Rec m <: Rec []

  -- <:width
  --   : ∀ {m n}
  --   → Rec m <: Rec n
  --   ---------------------------------
  --   → Rec ((x , A) ∷ m) <: Rec n

  -- <:depth
  --   : ∀ {m n}
  --   → Rec m <: Rec n
  --   → A <: B
  --   ---------------------------------
  --   → Rec ((x , A) ∷ m) <: Rec ((x , B) ∷ n)

  <:rec
    : {m n : Map Type}
    → n ⊆′ m
    -- → (∀ {e} (i : e ∈₁ m) (j : e ∈₁ n) → (lookup i <: lookup j))
    → All (λ { (k , v) → (i : k ∈ₖ′ m) → lookup′ i <: v}) n
    ---------------------------------
    → Rec m <: Rec n

  -- width
  --   : {m n : Map Type}
  --   → Rec m <: Rec n
  --   → ¬ (x ∈ₖ n)
  --   ---------------------------------
  --   → Rec ((x , A) ∷ m) <: Rec n

  -- depth
  --   : {m n : Map Type}
  --   → Rec m <: Rec n
  --   → A <: B
  --   → ¬ (x ∈ₖ m)
  --   → ¬ (x ∈ₖ n)
  --   ---------------------------------
  --   → Rec ((x , A) ∷ m) <: Rec ((x , B) ∷ n)

infix 3 _<:_

------------------------------------------------------------

{-# NON_TERMINATING #-}
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
... | no subtype = no λ { (<:rec _ s) → contradiction s (λ { (px ∷ᴬ f) → contradiction (px i) subtype })}
... | yes subtype with Rec m <:? Rec o
... | yes (<:rec s t) = yes (<:rec subset ((λ { j → lemma (∈ₖ′-irrelevant {_} {v} i j) subtype }) ∷ᴬ t))
  where
    lemma : ∀ {m : Map Type} {i j : x ∈ₖ′ m} → i ≡ j → lookup′ {Type} {x} {m} i <: A → lookup′ {Type} {x} {m} j <: A
    lemma refl s = s
... | no m<:o = no (m<:o ∘ λ { (<:rec (px ∷ᴬ s) (px₁ ∷ᴬ t)) → <:rec s t })

------------------------------------------------------------
-- Properties of _<:_

-- <:-refl : Reflexive _<:_
-- <:-refl {`⊤} = <:⊤ {`⊤}
-- <:-refl {`ℕ} = <:ℕ
-- <:-refl {`ℤ} = <:ℤ
-- <:-refl {arg ⇒ body} = <:⇒ <:-refl <:-refl
-- <:-refl {Rec x} = <:rec {!!} {!!}

-- <:-trans : Transitive _<:_
-- <:-trans i<:j j<:k = {!!}

-- <:antisym : Antisymmetric _≈_ _<:_
-- <:antisym _ refl = refl
-- <:antisym refl _ = refl
-- <:antisym (trans i<:j j<:k) (trans k<:j j<:i) = {!trans!}
-- <:antisym (width x) (trans sub sub₁) = {!!}
-- <:antisym (depth eq eq₁ x x₁) (trans sub sub₁) = {!!}
-- -- <:antisym eq (perm x) = {!!}
-- <:antisym eq (width x) = {!!}
-- <:antisym eq (depth sub sub₁ x x₁) = {!!}

------------------------------------------------------------

data _⊢_::_ (Γ : Context Type α) : Term α → Type → Set where
  -- propertes of contexts
  -- ⊢permute : (Δ : Context Type α)
  --   → Γ ⊢ v :: A
  --   → Γ ↭ Δ
  --   ---------------------------------
  --   → Δ ⊢ v :: A


  ⊢`
    : (p : x ∈ α)
    ---------------------------------
    → Γ ⊢ ` x # p :: lookupVar Γ x p

  ⊢ƛ
    : Γ , x :: A ⊢ u :: B
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
    : {rs : Map (Term α)} {rt : Map Type}
    → ¬ (x ∈ₖ rs)
    → Γ ⊢ rec rs :: Rec rt
    → Γ ⊢ v :: A
    ---------------------------------
    → Γ ⊢ rec ((x , v) ∷ rs) :: Rec ((x , A) ∷ rt)

  ⊢get
    : {r : Map Type} (p : x ∈ₖ r)
    -- → Γ ⊢ v :: Rec ((Γₕ , x :: a) ⊕ Γₜ)
    → Γ ⊢ v :: Rec r
    ---------------------------------
    → Γ ⊢ get x v :: lookup p

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
