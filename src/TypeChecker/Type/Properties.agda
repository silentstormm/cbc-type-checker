open import Relation.Binary using (DecidableEquality)

module TypeChecker.Type.Properties {name : Set} (_≟ₙ_ : DecidableEquality name) where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)
open import Relation.Nullary using (yes; no; contradiction)

open import TypeChecker.Type

-- there has to be a better way to do this
_≟_ : DecidableEquality Type
`⊤ ≟ `⊤ = yes refl
`⊤ ≟ `ℕ = no (λ ())
`⊤ ≟ `ℤ = no (λ ())
`⊤ ≟ (b ⇒ b₁) = no (λ ())
`⊤ ≟ Rec x = no (λ ())
`ℕ ≟ `⊤ = no (λ ())
`ℕ ≟ `ℕ = yes refl
`ℕ ≟ `ℤ = no (λ ())
`ℕ ≟ (b ⇒ b₁) = no (λ ())
`ℕ ≟ Rec x = no (λ ())
`ℤ ≟ `⊤ = no (λ ())
`ℤ ≟ `ℕ = no (λ ())
`ℤ ≟ `ℤ = yes refl
`ℤ ≟ (b ⇒ b₁) = no (λ ())
`ℤ ≟ Rec x = no (λ ())
(a ⇒ a₁) ≟ `⊤ = no (λ ())
(a ⇒ a₁) ≟ `ℕ = no (λ ())
(a ⇒ a₁) ≟ `ℤ = no (λ ())
(a ⇒ b) ≟ (c ⇒ d) with a ≟ c | b ≟ d
... | no ¬p | no ¬q = no (λ { refl → contradiction refl ¬p })
... | no ¬p | yes refl = no (λ { refl → contradiction refl ¬p })
... | yes refl | no ¬q = no (λ { refl → contradiction refl ¬q })
... | yes refl | yes refl = yes refl
(a ⇒ a₁) ≟ Rec x = no (λ ())
Rec x ≟ `⊤ = no (λ ())
Rec x ≟ `ℕ = no (λ ())
Rec x ≟ `ℤ = no (λ ())
Rec x ≟ (b ⇒ b₁) = no (λ ())
-- does not pass termination :(
-- Rec x ≟ Rec y with decidable (≡-dec _≟ₙ_ _≟_) x y
-- ... | no ¬eq = no {!!}
-- ... | yes eq = yes {!!}
Rec [] ≟ Rec [] = yes refl
Rec [] ≟ Rec (x ∷ y) = no (λ ())
Rec (x ∷ xs) ≟ Rec [] = no (λ ())
Rec ((kx , vx) ∷ xs) ≟ Rec ((ky , vy) ∷ ys) with kx ≟ₙ ky | vx ≟ vy | Rec xs ≟ Rec ys
... | no ¬p | no ¬q | no ¬r = no (λ { refl → contradiction refl ¬p })
... | no ¬p | yes refl | no ¬r = no (λ { refl → contradiction refl ¬p })
... | yes refl | no ¬q | no ¬r = no (λ { refl → contradiction refl ¬q })
... | yes refl | yes refl | no ¬eq = no (λ { refl → contradiction refl ¬eq })
... | no ¬p | no ¬q | yes refl = no (λ { refl → contradiction refl ¬p })
... | no ¬p | yes refl | yes refl = no (λ { refl → contradiction refl ¬p })
... | yes refl | no ¬q | yes refl = no (λ { refl → contradiction refl ¬q })
... | yes refl | yes refl | yes refl = yes refl
