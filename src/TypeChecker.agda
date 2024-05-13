open import Relation.Binary

module TypeChecker {name : Set} (_≟_ : DecidableEquality name) where

open import Agda.Primitive
open import Agda.Builtin.Equality

open import Data.Bool using (Bool)
open import Data.Product using (Σ-syntax; _,_)
open import Data.List using (_∷_)
open import Data.List.Relation.Unary.All renaming (_∷_ to _∷ᴬ_)
open import Data.Sum.Base
open import Effect.Monad
open import Function.Base using (_∘′_)
open RawMonad ⦃ ... ⦄
open import Relation.Nullary.Decidable

open import Term {name}
open import TypeChecker.Type {name}
open import TypeChecker.TypingRules {name}
open import Util.Context {name}
open import Util.Evaluator
open import Util.Scope

private variable
  α : Scope name
  u : Term α

-- Type checking function application requires conversion checking,
-- i.e. checking whether two types are equal.
--
convert : (a b : Type) → Evaluator (a ≡ b)
convert `ℕ `ℕ = return refl
convert (la ⇒ lb) (ra ⇒ rb) = do
  refl ← convert la ra
  refl ← convert lb rb
  return refl
convert _ _ = evalError "unequal types"

getFromContext : ∀ (Γ : Context Type α) (k : name) → Evaluator (Σ[ index ∈ (k ∈ α) ] Type)
getFromContext [] k = evalError  "record does not have the requested key"
getFromContext {x ∷ β} (t ∷ᴬ ctx) k with x ≟ k
... | yes refl = return (here , t)
... | no ¬a = (λ (p , ty) → there p , ty) <$> (getFromContext ctx k)
-- then return ({! here!} , {!!}) else {! !}

-- Bidirectional style type checking, with two functions defined mutually.
--
-- Both functions return a typing judgement for the specific input term,
-- so we know that we get a correct typing derivation 
-- but also that it is a derivation for the given input(s).
inferType : ∀ (Γ : Context Type α) u             → Evaluator (Σ[ t ∈ Type ] Γ ⊢ u :: t)
checkType : ∀ (Γ : Context Type α) u (ty : Type) → Evaluator (Γ ⊢ u :: ty)

inferType ctx (` x # index) = return (lookupVar ctx x index , ⊢` index)
inferType ctx (ƛ x ⇒ body) = evalError "cannot infer the type of a lambda"
inferType ctx (lam · arg) = do
  (a ⇒ b) , gtu ← inferType ctx lam
    where _ → evalError "application head should have a function type"
  gtv ← checkType ctx arg a
  return (b , ⊢· gtu gtv)
inferType ctx (rec []) = return (Rec [] , ⊢rec-empty)
inferType {α} ctx (rec {k ∷ β} (v ∷ᴬ c)) =
  (λ {
    (vt , vr) (Rec .∅ , ⊢rec-empty) → (Rec {k ∷ β} (∅ , k :: vt) , ⊢rec-more ⊢rec-empty vr) ;
    (vt , vr) (Rec rc , ⊢rec-more rr rr₁) → (Rec {k ∷ β} (rc , k :: vt) , ⊢rec-more (⊢rec-more rr rr₁) vr)
  }) <$> inferType ctx v <*> inferType ctx (rec {α} {β} c)
inferType ctx (get k r) with inferType ctx r
... | inj₁ e = evalError e
... | inj₂ (_ , ⊢rec-empty) = evalError "record does not have the requested key" -- TODO say what key
... | inj₂ (Rec c , rule) = do
  (t , index) ← getFromContext c k
  return (lookupVar c k t , ⊢get t rule)
... | _ = evalError "cannot get from non-record" -- TODO impl `show Type` to say what type

checkType ctx (ƛ x ⇒ body) (a ⇒ b) = do
  tr ← checkType (ctx , x :: a) body b
  return (⊢ƛ tr)
checkType ctx (ƛ _ ⇒ _) _ = evalError "lambda should have a function type"
checkType ctx term ty = do
  (t , tr) ← inferType ctx term
  -- we call the conversion checker, which (if it succeeds) returns an equality proof,
  -- unifying the left- and right-hand sides of the equality for the remainder of the do-block
  refl ← convert t ty
  return tr
