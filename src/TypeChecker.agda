open import Relation.Binary using (DecidableEquality)

module TypeChecker {name : Set} (_≟_ : DecidableEquality name) where

open import Agda.Primitive
open import Agda.Builtin.Equality

open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ-syntax; _,_; proj₂; uncurry; _×_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Binary.Pointwise using (decidable)
open import Data.List.Relation.Unary.All using ([]) renaming (_∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum.Base using (inj₁; inj₂)
open import Effect.Monad
open import Function.Base using (_∘_; case_of_)
open RawMonad ⦃ ... ⦄
open import Relation.Nullary using (yes; no; Dec; map′; contradiction)

open import Term _≟_
open import TypeChecker.Type _≟_
open import TypeChecker.TypingRules _≟_
open import Util.Context {name}
open import Util.Evaluator
open import Util.Map _≟_
open import Util.Scope

private variable
  α : Scope name
  u : Term α

-- Type checking function application requires conversion checking,
-- i.e. checking whether two types are equal.
--
convert : (a b : Type) → Evaluator (a ≡ b)
convertMap : (ma mb : Map Type) → Evaluator (ma ≡ mb)
convertKV : (pa pb : name × Type) → Evaluator (pa ≡ pb)

convertKV (ka , ta) (kb , tb) with ka ≟ kb
... | yes refl = do
  refl ← convert ta tb
  return refl
... | no ¬a = evalError "record fields unequal"

convertMap [] [] = return refl
convertMap [] (b ∷ bs) = evalError "record has too many fields"
convertMap (a ∷ as) [] = evalError "record has too many fields"
convertMap (a ∷ as) (b ∷ bs) = do
  refl ← convertKV a b
  refl ← convertMap as bs
  return refl

convert `ℕ `ℕ = return refl
convert `ℤ `ℤ = return refl
convert (la ⇒ lb) (ra ⇒ rb) = do
  refl ← convert la ra
  refl ← convert lb rb
  return refl
convert (Rec a) (Rec b) = do
  refl ← convertMap a b
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
inferType : ∀ (Γ : Context Type α) u → Evaluator (Σ[ t ∈ Type ] Γ ⊢ u :: t)
checkType : ∀ (Γ : Context Type α) u (t : Type) → Evaluator (Σ[ s ∈ Type ] (s <: t × Γ ⊢ u :: s))

inferType ctx (` x # index) = return (lookupVar ctx x index , ⊢` index)
inferType ctx (ƛ x :: ty ⇒ body) = do
  vt , vrule ← inferType (ctx , x :: ty) body
  return ((ty ⇒ vt) , ⊢ƛ vrule)
inferType ctx (lam · arg) = do
  (a ⇒ b) , lamrule ← inferType ctx lam
    where _ → evalError "application head should have a function type"
  (_ , argsub , argrule) ← checkType ctx arg a
  return (b , ⊢· lamrule argrule argsub)
-- with inferType ctx lam
-- ... | inj₁ x with x == "cannot infer the type of a lambda" = {!!}
-- ...| inj₂ y = {!!}
inferType ctx (rec []) = return (Rec [] , ⊢rec-empty)
inferType ctx (rec ((k , v) ∷ c)) with inferType ctx v | inferType ctx (rec c)
... | inj₁ e | _  = evalError e
... | _ | inj₁ e  = evalError e
... | inj₂ (vt , vr) | inj₂ (rt , rr) with k ∈ₖ? c
... | yes i = evalError "records cannot have duplicate keys"
... | no ¬i with rt
... | Rec tm = return (Rec ((k , vt) ∷ tm) , ⊢rec-more ¬i rr vr)
... | _ = evalError "unreachable"
inferType ctx (get k r) with inferType ctx r
... | inj₁ e = evalError e
... | inj₂ (Rec m , rule) with k ∈ₖ? m
... | no ¬a = evalError "record does not have the requested key"
... | yes i = return (lookup i , ⊢get i rule)
inferType ctx (get k r) | _  = evalError "get needs a record" -- TODO impl `show Type` to say what type
inferType ctx `zero = return (`ℕ , ⊢zero)
inferType ctx (`suc n) = do
  `ℕ , rule ← inferType ctx n
    where _ → evalError "suc needs an natural"
  return (`ℕ , ⊢suc rule)
inferType ctx (`pos n) = do
  `ℕ , rule ← inferType ctx n
    where _ → evalError "pos needs an natural"
  return (`ℤ , ⊢pos rule)
inferType ctx (`negsuc n) = do
  `ℕ , rule ← inferType ctx n
    where _ → evalError "negsuc needs an natural"
  return (`ℤ , ⊢negsuc rule)

checkType ctx term t with inferType ctx term
... | inj₁ e = evalError e
... | inj₂ (s , r) with s <:? t
... | yes sub = return (s , sub , r)
... | no sub = evalError "mismatched types"
