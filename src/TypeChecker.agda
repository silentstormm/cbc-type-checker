open import Relation.Binary using (DecidableEquality)

module TypeChecker {name : Set} (_≟ₙ_ : DecidableEquality name) where

open import Agda.Primitive
open import Agda.Builtin.Equality

open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ-syntax; _,_; proj₂; uncurry; _×_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Binary.Pointwise using (decidable)
open import Data.List.Relation.Unary.All using ([]) renaming (_∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.First as First using ()
open import Data.Sum.Base using (inj₁; inj₂)
open import Effect.Monad
open import Function.Base using (_∘_; case_of_)
open RawMonad ⦃ ... ⦄
open import Relation.Nullary using (yes; no; Dec; map′; contradiction; contraposition)

open import Term
open import Term.Properties _≟ₙ_ renaming (_≟_ to _≟ᵤ_)
open import TypeChecker.Type {name}
open import TypeChecker.Type.Properties _≟ₙ_ renaming (_≟_ to _≟ₜ_)
open import TypeChecker.TypingRules _≟ₙ_
open import Util.Context {name}
open import Util.Evaluator
open import Util.Map _≟ₙ_ _≟ₜ_
open import Util.Map _≟ₙ_ _≟ᵤ_ as Record using () renaming (Map to Record)
open import Util.Scope

private variable
  α : Scope name
  u : Term

infer? : ∀ (Γ : Map) u → Dec (Σ[ t ∈ Type ] Γ ⊢ u :: t)
check? : ∀ (Γ : Map) u (t : Type) → Dec (Σ[ s ∈ Type ] (s <: t × Γ ⊢ u :: s))

infer? ctx (` x) with x ∈ₖ′? ctx
... | no ¬i = no λ { (t , ⊢` _ i _) → contradiction i ¬i }
... | yes i = yes (lookup′ i , ⊢` (∈ₖ′⇒∈′ i refl) i refl)
infer? ctx (ƛ x :: ty ⇒ body) with infer? ((x , ty) ∷ ctx) body
... | no ¬r = no λ { (.(ty ⇒ _) , ⊢ƛ {B = B} r) → contradiction (B , r) ¬r }
... | yes (vt , vr) = yes ((ty ⇒ vt) , ⊢ƛ vr)
infer? ctx (lam · arg) with infer? ctx lam
... | no ¬lam = no λ { (appt , ⊢· {A = A} l _ _) → contradiction ((A ⇒ appt) , l) ¬lam }
... | yes (`⊤ , fr) = no (λ { (t , ⊢· lr _ _) → contradiction (⊢type-irrelevant lr fr) λ () })
... | yes (`ℕ , fr) = no (λ { (t , ⊢· lr _ _) → contradiction (⊢type-irrelevant lr fr) λ () })
... | yes (`ℤ , fr) = no (λ { (t , ⊢· lr _ _) → contradiction (⊢type-irrelevant lr fr) λ () })
... | yes (Rec x , fr) = no (λ { (t , ⊢· lr _ _) → contradiction (⊢type-irrelevant lr fr) λ () })
... | yes ((a ⇒ b) , lamrule) with check? ctx arg a
... | no ¬arg = no λ { (appt , ⊢· {A = A} {C = C} lr ar s) → case A ≟ₜ a of λ
  { (no ¬eq) → contradiction (get-arg (⊢type-irrelevant lr lamrule)) ¬eq
  ; (yes refl) → contradiction (C , s , ar) ¬arg
  } }
  where
    get-arg : ∀ {A B C D} → (A ⇒ B) ≡ (C ⇒ D) → A ≡ C
    get-arg refl = refl
... | yes (_ , argsub , argrule) = yes (b , ⊢· lamrule argrule argsub)
infer? ctx (rec []) = yes (Rec [] , ⊢rec-empty)
infer? ctx (rec ((k , v) ∷ c)) with infer? ctx v | infer? ctx (rec c)
... | no ¬v | _  = no λ { (.(Rec ((k , _) ∷ _)) , ⊢rec-more {A = A} i rr rv) → contradiction (A , rv) ¬v }
... | _ | no ¬r  = no λ { (.(Rec ((k , _) ∷ _)) , ⊢rec-more {rt = rt} i rr rv) → contradiction (Rec rt , rr) ¬r }
... | yes (vt , vr) | yes (Rec .[] , ⊢rec-empty) = yes (Rec ((k , vt) ∷ []) , ⊢rec-more (λ ()) ⊢rec-empty vr)
... | yes (vt , vr) | yes (Rec rt , rr) with k ∈ₖ′? rt
... | yes i = no λ { (t , ⊢rec-more {rt = r} ¬i recr newr) → case Rec rt ≟ₜ Rec r of λ
  { (no ¬eq) → contradiction (⊢type-irrelevant rr recr) ¬eq
  ; (yes refl) → contradiction i ¬i
  } }
... | no ¬i = yes (Rec ((k , vt) ∷ rt) , ⊢rec-more ¬i rr vr)
infer? ctx (get k r) with infer? ctx r
... | no ¬r = no λ { (_ , ⊢get {r = r} p q eq gr) → contradiction (Rec r , gr) ¬r }
... | yes (`⊤ , rr) = no (λ { (t , ⊢get _ _ _ r) → contradiction (⊢type-irrelevant r rr) λ () })
... | yes (`ℕ , rr) = no (λ { (t , ⊢get _ _ _ r) → contradiction (⊢type-irrelevant r rr) λ () })
... | yes (`ℤ , rr) = no (λ { (t , ⊢get _ _ _ r) → contradiction (⊢type-irrelevant r rr) λ () })
... | yes ((a ⇒ b) , rr) = no (λ { (t , ⊢get _ _ _ r) → contradiction (⊢type-irrelevant r rr) λ () })
... | yes (Rec m , rr) with k ∈ₖ′? m
... | no ¬i = no λ { (_ , ⊢get {r = r} _ i refl rule) → case Rec m ≟ₜ Rec r of λ
  { (no ¬eq) → contradiction (⊢type-irrelevant rr rule) ¬eq
  ; (yes refl) → contradiction i ¬i
  } }
... | yes i = yes (lookup′ i , ⊢get (∈ₖ′⇒∈′ i refl) i refl rr)
infer? ctx `zero = yes (`ℕ , ⊢zero)
infer? ctx (`suc n) with infer? ctx n
... | yes (`ℕ , r) = yes (`ℕ , ⊢suc r)
... | yes (`⊤ , r) = no λ { (`ℕ , ⊢suc nr) → contradiction (⊢type-irrelevant r nr) λ () }
... | yes (`ℤ , r) = no λ { (`ℕ , ⊢suc nr) → contradiction (⊢type-irrelevant r nr) λ () }
... | yes ((_ ⇒ _) , r) = no λ { (`ℕ , ⊢suc nr) → contradiction (⊢type-irrelevant r nr) λ () }
... | yes (Rec x , r) = no λ { (`ℕ , ⊢suc nr) → contradiction (⊢type-irrelevant r nr) λ () }
... | no ¬n = no λ { (`ℕ , ⊢suc nr) → contradiction (`ℕ , nr) ¬n }
infer? ctx (`pos n) with infer? ctx n
... | yes (`ℕ , r) = yes (`ℤ , ⊢pos r)
... | yes (`⊤ , r) = no λ { (nt , ⊢pos nr) → contradiction (⊢type-irrelevant r nr) λ () }
... | yes (`ℤ , r) = no λ { (nt , ⊢pos nr) → contradiction (⊢type-irrelevant r nr) λ () }
... | yes ((_ ⇒ _) , r) = no λ { (nt , ⊢pos nr) → contradiction (⊢type-irrelevant r nr) λ () }
... | yes (Rec x , r) = no λ { (nt , ⊢pos nr) → contradiction (⊢type-irrelevant r nr) λ () }
... | no ¬n = no λ { (`ℤ , ⊢pos nr) → contradiction (`ℕ , nr) ¬n }
infer? ctx (`negsuc n) with infer? ctx n
... | yes (`ℕ , r) = yes (`ℤ , ⊢negsuc r)
... | yes (`⊤ , r) = no λ { (`ℤ , ⊢negsuc nr) → contradiction (⊢type-irrelevant r nr) λ () }
... | yes (`ℤ , r) = no λ { (nt , ⊢negsuc nr) → contradiction (⊢type-irrelevant r nr) λ () }
... | yes ((_ ⇒ _) , r) = no λ { (nt , ⊢negsuc nr) → contradiction (⊢type-irrelevant r nr) λ () }
... | yes (Rec x , r) = no λ { (nt , ⊢negsuc nr) → contradiction (⊢type-irrelevant r nr) λ () }
... | no ¬n = no λ { (`ℤ , ⊢negsuc nr) → contradiction (`ℕ , nr) ¬n }

check? ctx term t with infer? ctx term
... | no ¬term = no λ { (t , s , r) → contradiction (t , r) ¬term }
... | yes (s , r) with s <:? t
... | no ¬sub = no λ { (ty , sub , rule) → case s ≟ₜ ty of λ
  { (no ¬eq) → contradiction (⊢type-irrelevant r rule) ¬eq
  ; (yes refl) → contradiction sub ¬sub
  } }
... | yes sub = yes (s , sub , r)
