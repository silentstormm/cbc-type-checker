# Correct-by-Construction Type Checking

This repository contains a small example of a correct-by-construction type checker for the [simply-typed lambda calculus](https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus) with records and subtyping implemented in [Agda](https://agda.readthedocs.io/en/latest/index.html).

## Setup

To get the code working, follow these steps:

1. Install Agda by following [the instruction on the website](https://agda.readthedocs.io/en/latest/getting-started/installation.html).
2. Install the `standard-library` using the [installation guide](https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md).
3. To test that everything works, compile the `src/Everything.agda` file.

## Overview

The type checker is built up using various components, outlined below.
A small example where the type checker is used can be found in the `Everything` module.

### `Util.Map` and `Util.Map.KeyValue`

We define an association list data structure for variable contexts and records:

```agda
module Util.Map.KeyValue {K V : Set} (_≟ₖ_ : DecidableEquality K) (_≟ᵥ_ : DecidableEquality V) where

KV : Set
KV = K × V

module Util.Map {K V : Set} (_≟ₖ_ : DecidableEquality K) (_≟ᵥ_ : DecidableEquality V) where

Map : Set
Map = List KV
```

To be able to find the latest binding of a variable in a `Map`, we define a few memberships based on `First` from the standard library.

```agda
_∈′_ : KV → Map → Set
_∈′_ x = First (x ≢_) (x ≡_)

_∈ₖ′_ : K → Map → Set
_∈ₖ′_ k = First (k ≢ₖ_) (k ≡ₖ_)

_∈ₖ′?_ : Decidable _∈ₖ′_
_∈ₖ′?_ k = cofirst?  ((k ≟ₖ_) ∘ proj₁)

_∈₁′_ : KV → Map → Set
_∈₁′_ k = First (k ≢₁_) (k ≡₁_)
```

### `Term` and `TypeChecker.Type`

We construct a syntax for the language:

```agda
data Type : Set where
  `⊤ : Type
  `ℕ : Type
  `ℤ : Type
  _⇒_ : (a b : Type) → Type
  Rec : List (name × Type) → Type
  
data Term : Set where
  `_ : name → Term
  ƛ_::_⇒_ : name → Type → Term → Term
  _·_   : (f a : Term) → Term
  rec : List (name × Term) → Term
  get : name → Term → Term
  `zero : Term
  `suc : Term → Term
  `pos : Term → Term
  `negsuc : Term → Term
```

The `Term.Properties` and `Typechecker.Type.Properties` modules define a `DecidableEquality` for `Term`s and `Type`s repectively.

### `TypeChecker.TypingRules`

Next, we specify the typing rules of the language:

```agda
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
```

Now we can write `Γ ⊢ u ∶ t` for `u` has type `t` under context `Γ` and `S <: T` for `S` is a subtype of `T`.

We also define `_<:?_`, a decider for `_<:_` and `⊢type-irrelevant`, a lemma stating that two typing rules with the same context and term derive the same type.

### `TypeChecker`

Finally, we define the [bidirectional-style type checking functions](https://plfa.github.io/Inference/) mutually:

```agda
infer : ∀ (Γ : Map) u → Dec (Σ[ t ∈ Type ] Γ ⊢ u :: t)
check : ∀ (Γ : Map) u (t : Type) → Dec (Σ[ s ∈ Type ] (s <: t × Γ ⊢ u :: s))
```

Things to note:
* Both `infer` and `check` return a typing judgement for the specific input term (and type, in case of `check`), so we know not just that we get a correct typing derivation but also that it is a derivation for the given input(s).
* We provide the relevant typing and subtyping rules on success and evidence of a contradiction in the negative cases, so our type checker is _sound_ and _complete_, i.e. regardless of whether it accepts or rejects, we know it is correct.
