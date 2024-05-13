module TypeChecker.TypingRules {name : Set} where

open import Term {name}
open import TypeChecker.Type {name}
open import Util.Context {name}
open import Util.Scope

private variable
  x : name
  α : Scope name
  a b : Type
  u v : Term α

-- type \|- to type ⊢
data _⊢_::_ (Γ : Context Type α) : Term α → Type → Set where
  ⊢`
    : (p : x ∈ α)
    ---------------------------------
    → Γ ⊢ ` x # p :: lookupVar Γ x p

  ⊢ƛ
    : Γ , x :: a ⊢ u :: b
    ---------------------------------
    → Γ ⊢ (ƛ x ⇒ u) :: a ⇒ b

  ⊢·
    : Γ ⊢ u :: (a ⇒ b)
    → Γ ⊢ v :: a
    ---------------------------------
    → Γ ⊢ u · v :: b

  -- ⊢rec
  --   : {β : Scope name} {γₛ : Context (Term α) β} {γₜ : Context Type β}
  --   → Γ ⊢ rec β γₛ ∶ Rec β γₜ

  ⊢rec-empty
    : Γ ⊢ rec ∅ :: Rec ∅

  ⊢rec-more
    : {β : Scope name} {Γₛ : Context (Term α) β} {Γₜ : Context Type β}
    → Γ ⊢ rec Γₛ :: Rec Γₜ
    → Γ ⊢ v :: a
    ---------------------------------
    → Γ ⊢ rec (Γₛ , x :: v) :: Rec (Γₜ , x :: a)

  ⊢get
    : {β : Scope name} {Γᵣ : Context Type β} (p : x ∈ β)
    -- → Γ ⊢ v :: Rec ((Γₕ , x :: a) ⊕ Γₜ)
    → Γ ⊢ v :: Rec Γᵣ
    ---------------------------------
    → Γ ⊢ get x v :: lookupVar Γᵣ x p

infix 3 _⊢_::_
