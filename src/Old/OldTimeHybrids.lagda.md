# Formalizing Fred Van Oystaeyen's "Time Hybrids"

This document presents a *formalization* of a *mathematical abstraction* of the *basics* of
Fred Van Oystaeyen's book, *Time Hybrids: A New Generic Theory of Reality*.

Fred, an outstanding mathematician is a pioneer on *noncommutative algebraic geometry*. Among
others he wrote the book *Virtual topology and Functor geometry* that contributes to the
underlying a mathematical abstraction of his Time Hybrids book.

My goal was to formalize the underlying mathematical abstraction of the basics of Fred's book
*computationally* in a *constructive* and *pointfree* way.

Frankly, my mathematical abstraction is not fully in synch with Fred's mathematical
abstraction.

## Choices

There are two fundamental design choices in this formalization:

### 1. The Mathematical Abstraction

Please read diagonally if you are not inclined. 

We model Fred's Reality using the following mathematical abstractions:

- **Categories**: Both the *virtual universe* and the *material universe* are modeled as
  categories.

- **Transitions**: *Dynamic evolution* is modeled as *transitions*, which are categorical 
  *endomorphisms* (morphisms from an object to itself).

- **Functors**: The evolution of *universe entities* — such as virtual *pre-places* and
  material *pre-thing-collections* — is governed by *functors* that map 
  *virtual universe transitions* to their respective *entity transitions*.

- **Profunctors**: The inter-action between the virtual and material universes is modeled
  pointfree as a *profunctor*. 
  
- **Heteromorphisms**: More precisely, the cross-category connection between
  pre-thing-collections and pre-places is modeled as a *heteromorphism*, upon which material
  pre-thing-collection transitions and virtual pre-place transitions act on the left and right,
  respectively.

Note that I we used the word "inter-action" instead of "interaction". The word "inter-action"
is used to emphasize that both pre-thing-collections and pre-places act upon their
cross-category connection. The word interaction which will be introduced later.

### 2. The Formal Framework

Please read diagonally if you are not inclined. 

We formalize this modeleling in **`Cubical Agda`** rather than standard `Agda` or `Lean 4`,
motivated by several constructive computational principles:

- **Computational Path Equality**: In `Cubical Agda`, equality is not an inductive identity
  type, but a *path* over an *abstract interval dimension* `I`. *Structural recursion*
  computes directly using `transport` along paths.

- **Computational Univalence**: The *Univalence Principle* establishes that type equivalence
  (`_≃_`) is equivalent to path equality (`_≡_`). In `Cubical Agda`, univalence computes
  natively via `ua` and `pathToEquiv`, allowing structural equivalences to be converted
  into path equalities without unproven classical axioms.

- **Harmonizing Paths and Transitions**: Category theory provides transitions at which
  states evolve, while Homotopy Type Theory provides paths along which equality and
  structure are transported. In our formalization, these two concepts work in complete harmony:
  paths between types are lifted to paths between transition types, allowing dynamic state
  changes to be transported across universes.

## Structure of the Formalization

So far, the formalization proceeds in five modular stages:

1. **Primary Foundations & Core Abstractions**: Basic category theory primitives,
   transition mappings, and algebraic structures (`Zero`, `IsMonad`, `Choices`, `Supremum`).

2. **The `Reality` Specification**: The abstract interface defining the virtual and
   material universes, their profunctor interaction, and transition transport.

3. **Structural Properties & Univalence**: Preservation laws, absorption properties,
   order preservation, and the univalent equivalence of property formulations.

4. **Discrete Intervals & Pre-Ordered Reality**: Formalizing discrete time intervals, gaps,
   and ordered reality structures.

5. **Concrete Realization**: Realizing the abstract specification using Kuratowski finite
   sets (`LFSet`) in the category of sets and functions (`SET₀`).

## Leveraging existing `Cubical Agda` modules as much as possible

We leverage standard libraries to keep definitions idiomatic and constructive:
- Categories, functors, natural transformations, and monads from `Cubical.Categories`.
- Profunctors and heteromorphisms from `Cubical.Categories.Profunctor`.
- Binary relations and preorders from `Cubical.Relation.Binary.Order`.
- Univalence and equivalence paths from `Cubical.Foundations`.

## Core Abstractions

```agda
{-# OPTIONS --cubical --guardedness #-}

module OldTimeHybrids where
```

### Primary Category Theory Foundations

We introduce the minimal categorical foundations needed to begin:

- Universe levels from `Agda.Primitive`.
- Path equality and cubical type theory primitives from `Cubical.Foundations.Prelude`.
- `Category` and hom-types `_[_,_]` from `Cubical.Categories.Category.Base`.
- `Functor` and endofunctor operations (`_⟅_⟆`, `_⟪_⟫`, `Id`, `_∘F_`) from
  `Cubical.Categories.Functor.Base`.
- `NatTrans` and identity natural transformations (`idTrans`) from
  `Cubical.Categories.NaturalTransformation.Base`.

Note that the universe levels above have nothing to do with the virtual and material universes.
They are used to avoid paradoxes in type theory by building a hierarchy of theories.

```agda
open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to ℓ-max)

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base using (Category; _[_,_])
open import Cubical.Categories.Functor.Base as CubicalFunctor
  using (Functor; _⟅_⟆; _⟪_⟫; Id; _∘F_)
open import Cubical.Categories.NaturalTransformation.Base
  using (NatTrans; idTrans)
open import Cubical.Data.Unit
  using (Unit; tt; isSetUnit; isPropUnit; Unit*; tt*; isSetUnit*; isPropUnit*)
open import Cubical.Categories.Limits.Terminal
  using (Terminal; terminalOb; isTerminal; terminalArrow; terminalArrowUnique)

open import Cubical.Categories.Limits.Initial

open Category hiding (_∘_)

open NatTrans

record CategoryWithTerminal (o m : Level) : Type (lsuc (ℓ-max o m)) where
  field
    category : Category o m
    T        : Terminal category

  open Category category public

  1C : Category.ob category
  1C = T .fst

GlobalElement : ∀ {o m} (C : CategoryWithTerminal o m) →
  (Z : Category.ob (CategoryWithTerminal.category C)) → Type m
GlobalElement C Z =
  CategoryWithTerminal.category C [ CategoryWithTerminal.1C C , Z ]
```

### Naming conventions

We use verbose, sometimes long, names to, hopefully, make code easier to read.

Below is a first example, `transformationMorphism`.

```agda
transformationMorphism :
  ∀ {o₁ m₁ o₂ m₂} {C : Category o₁ m₁} {D : Category o₂ m₂}
    {F G : Functor C D}
  → NatTrans F G
  → ∀ (Z : ob C) → D [ F ⟅ Z ⟆ , G ⟅ Z ⟆ ]
transformationMorphism = N-ob
```

Note that

- For categories, we use names `C`, `D`, ... .
- For functors, we use names `F`, `G`, `H` ... .
- For objects, we use names `Z`, `Y`, `X` ... .

moreover

- For functions and morphisms, we will use names `f`, `g`, `h` ... .

Note that

- Everything introduced in parenthesis, `(` and `)`, is explicit.
- Everything introduced in curly braces, `{` and `}`, is implicit.

Note that

- `(Z : ob C)` could also have been `Z`. No parenthesis are needed, because `Agda`'s type
  system can infer the types `ob C`. `(Z : ob C)` shows that two categories, `C` and `D`,
  are involved.

### `TransitionMapping`

`record TransitionMapping` declares a `field` `transitionMapping`.

Given a category `C` and a functor `F : C → C`, `transitionMapping` maps transitions of an 
object `Z` to transitions of object `F ⟅ Z ⟆`. We also define `idTransitionMapping`,
the identity transition mapping.

```agda
record TransitionMapping
    {o m : Level}
    (C : Category o m)
    (F : Functor C C) : Type (ℓ-max o m) where
  field
    transitionMapping : ∀ {Z} → C [ Z , Z ] → C [ F ⟅ Z ⟆ , F ⟅ Z ⟆ ]

open TransitionMapping

idTransitionMapping :
    ∀ {o m} (C : Category o m)
  → (F : Functor C C)
  → TransitionMapping C F
idTransitionMapping C F =
  record { transitionMapping = λ {Z} _ → id C }
```

Note that, since there is only one category `C` involved, we omit type `Category.obj C`.

Also note that `{Z}` is implicit.

### `Zero`

`record Zero` formalizes *nothing*. I mean, it does formalizes something, but that something
is nothing.

It declares a natural transformation `field` `ζ`.

It also declares a law `zero-absorption`

- Composing any morphism `f` after `zero` yields `zero` (there's nothing after nothing).

`record Zero` formally abstracts the empty material universe.

We follow Fred to distinguish the *empty material universe* from the
*void (material universe)*. The void is not empty, there *are pre-things* in the void the but
there does not *exist things* in the void.

```agda
record Zero
    {o m : Level}
    (C : Category o m)
    (ZF : Functor C C) :
  Type (lsuc (ℓ-max o m)) where

  open Category C renaming (_∘_ to _∘C_)

  field
    ζ : NatTrans ZF ZF

  zero : (Z : Category.ob C) → C [ ZF ⟅ Z ⟆ , ZF ⟅ Z ⟆ ]
  zero = transformationMorphism ζ

  field
    zero-absorption :
      ∀ {Z : Category.ob C}
        (f : C [ ZF ⟅ Z ⟆ , ZF ⟅ Z ⟆ ])
      → f ∘C zero Z ≡ zero Z

open Zero {{...}} public
```

### `Choices`

`record Choices` formally abstracts collecting all choices of pre-things from all
pre-thing-collections of a collection of non-empty pre-thing-collections.

It declares a natural transformation `field` `χ`.

It also declares a law `choices-union-absorption`

- Composing `union` after `choices` yields `union`.

To formally abstract the `union` operation (and, later on, also the `singleton`
operation), we use the categorical notion of a functor being a *monad*. A monad is a functor
equipped with a *multiplication* natural transformation `μ` and a *unit*  natural
transformation `η`.

```agda
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Categories.Monad.Base using (IsMonad)

open IsMonad using (μ; η)
```

```agda
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Categories.Monad.Base using (IsMonad)

open IsMonad
```

```agda
record Choices
    {o m : Level}
    (C : Category o m)
    (ChF : Functor C C)
    (isMonad : IsMonad ChF) :
      Type (lsuc (ℓ-max o m)) where

  open Category C renaming (id to idC; _∘_ to _∘C_)

  union : (Z : Category.ob C) → C [ (ChF ∘F ChF) ⟅ Z ⟆ , ChF ⟅ Z ⟆ ]
  union = transformationMorphism (μ isMonad)

  field
    χ : NatTrans (ChF ∘F ChF) (ChF ∘F ChF)

  choices : (Z : Category.ob C) → C [ (ChF ∘F ChF) ⟅ Z ⟆ , (ChF ∘F ChF) ⟅ Z ⟆ ]
  choices = transformationMorphism χ

  field
    choices-union-absorption :
      ∀ {Z : Category.ob C}
      → union Z ∘C choices Z ≡ union Z

open Choices {{...}} public
```

### `Supremum`

We also define `record Supremum` for pointfree suprema.

It declares a morphism `field` `supremum`.

```agda
record Supremum
    {o m : Level}
    (C : Category o m)
    (CF : Functor C C)
    (Z : Category.ob C) :
      Type (lsuc (ℓ-max o m)) where
  field
    supremum : C [ CF ⟅ Z ⟆ , Z ]

open Supremum {{...}} public
```

## The `Reality` Specification

The central specification `record Reality` brings together the *virtual universe*, the
*material universe*, and how they *act upon each other*.

### The `Reality` model

For dealing with the *inter-action* of the virtual and material universes, we need to `import`:

- **Profunctors** (`Cubical.Categories.Profunctor.Base`) to formalize heteromorphic
  inter-actions between two distinct categories.

```agda
open import Cubical.Categories.Profunctor.Base
  using (Profunctor⊶; module Profunctor⊶)
```

For dealing with various pre-ordered-sets, we need to `import`:

- **Preorders** (`Cubical.Relation.Binary.Order.Proset`) to formalize the preorder of,
  among others, transitions.

```agda
open import Cubical.Relation.Binary.Order.Proset
  using (ProsetStr; module ProsetStr; IsProset; module IsProset; prosetstr)

open ProsetStr {{...}} public
```

For dealing with various product types, we need to `import`:

- **Product types** `_×_` (`Cubical.Data.Sigma`), among others, to formalize composite
  predicates (cfr. the *Curry Howard Isomorphism*).

```agda
open import Cubical.Data.Sigma using (_×_)
```

For dealing with various instances to univalence, we need to `import`:

- **Univalence** (`Cubical.Foundations.Equiv`, `Univalence`, `Isomorphism`)
  to convert between structural morphism equivalence (`_≃_`) and path equality (`_≡_`).

```agda
open import Cubical.Foundations.Equiv using (_≃_; invEquiv)
open import Cubical.Foundations.Univalence
  using (ua; pathToEquiv; univalence; ua-pathToEquiv; pathToEquiv-ua)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
```

`Reality` is parameterized by primary category parameters:

- `Cᵥ`: category of *virtual* *universe transitions*, *virtual*
  *pre-places* and collections thereof.
- `CWTₘ`: category with terminal of *material pre-things*, *pre-interactions* and
  collections thereof.

and generic collection and profunctor parameters:

- `CFᵥ`: virtual collection functor, formalizing to-collection mappings in the
  virtual universe.
- `CFₘ`: material collection functor, formalizing to-collection mappings in the
  material universe.
- `PFₘᵥ`: material-virtual profunctor, formalizing how the virtual universe acts upon the
  material universe and vice versa.

and parameters:

- `Uᵥ`: naming a unique designated virtual universe object.
- `Pₘ`: naming designated material objects, potentials, being atomic pre-thing objects above.

Think of `Uᵥ` as the *state* of the virtual universe or, maybe more spectacular,
as the *time* of the virtual universe.

Think of `Pₘ` non-existing atomic pre-things, being germs brewing what, eventually, will become
existing things.

Virtual universe transitions make the virtual universe dynamic.

Viewing virtual universe dynamics as state changes focusses on the *consequence* of changes.

Viewing virtual universe dynamics as time changes focusses on the *cause* of changes.

But, really, both views are essentially equivalent.

The code below also defines `_⋙ᵥ_ ` and ` _⋙ₘ_`, forward composition versions of `_∘ᵥ_` and
`_∘ₘ_`.

```agda
record Reality
    {o m : Level}
    (Cᵥ : Category o m)
    (CWTₘ : CategoryWithTerminal o m)
    (CFᵥ : Functor Cᵥ Cᵥ)
    (CFₘ : Functor (CategoryWithTerminal.category CWTₘ)
                   (CategoryWithTerminal.category CWTₘ))
    (PFₘᵥ : Profunctor⊶ o m (CategoryWithTerminal.category CWTₘ) Cᵥ)
    (Uᵥ : Category.ob Cᵥ)
    (Pₘ : Category.ob (CategoryWithTerminal.category CWTₘ)) :
      Type (lsuc (ℓ-max o m)) where

  open Category Cᵥ renaming (ob to obᵥ; id to idᵥ; _∘_ to _∘ᵥ_)

  _⋙ᵥ_ :
    ∀ {Z Y X : obᵥ}
    → Cᵥ [ Z , Y ]
    → Cᵥ [ Y , X ]
    → Cᵥ [ Z , X ]
  f ⋙ᵥ g = g ∘ᵥ f

  infixl 8 _⋙ᵥ_

  open CategoryWithTerminal CWTₘ
    renaming
      ( category to Cₘ
      ; ob to obₘ
      ; id to idₘ
      ; _∘_ to _∘ₘ_
      ; isSetHom to isSetHomₘ
      ; 1C to 1ₘ
      ; T to Tₘ
      )

  _⋙ₘ_ :
    ∀ {Z Y X : obₘ}
    → Cₘ [ Z , Y ]
    → Cₘ [ Y , X ]
    → Cₘ [ Z , X ]
  f ⋙ₘ g = g ∘ₘ f

  infixl 8 _⋙ₘ_
```

### Basic `field` declarations

- `prePlaceFunctor` formalizes mapping virtual *universe* transitions to virtual *pre-place*
   transitions, making pre-places dynamic.

and

- `preThingCollectionFunctor` formalizes mapping virtual *universe* transitions to material
   *pre-thing-collection* transitions, making pre-thing-collections dynamic.

and

- `PreThing` formalizes the generic pre-thing object in the material universe.

and

- `potentialAsPreThingMorphism` formalizes morphing an atomic *potential* into a
  *pre-thing*.

furthermore, `instance`s

- `materialCollectionIsMonad`, `materialCollectionZero` and `materialCollectionChoices`
  formalize collections and functions abstractions at material universe level (for functor
  `CFₘ`). More precisely of functionality like making singleton collections, making unions of
  collection of collections, mapping to empty collections and collecting all choices in all
  collections of collections of collections.

```agda
  field
    prePlaceFunctor :
      Functor Cᵥ Cᵥ

    preThingCollectionFunctor :
      Functor Cᵥ Cₘ

    PreThing : obₘ

    potentialAsPreThingMorphism :
      Cₘ [ Pₘ , PreThing ]

    instance
      materialCollectionIsMonad :
        IsMonad CFₘ

      materialCollectionZero :
        Zero Cₘ CFₘ

      materialCollectionChoices :
        Choices Cₘ CFₘ materialCollectionIsMonad

  open Profunctor⊶ PFₘᵥ
```

### Various synonyms

Below we define various synonyms that, hopefully, make the code more readable.

#### `obᵥ` or `obₘ` typed

```agda
  PrePlace : obᵥ
  PrePlace = prePlaceFunctor ⟅ Uᵥ ⟆

  PrePlaceCollection : obᵥ
  PrePlaceCollection = CFᵥ ⟅ PrePlace ⟆

  PreThingCollection : obₘ
  PreThingCollection = CFₘ ⟅ PreThing ⟆

  PreThingCollectionCollection : obₘ
  PreThingCollectionCollection = CFₘ ⟅ PreThingCollection ⟆

  PreThingCollectionCollectionCollection : obₘ
  PreThingCollectionCollectionCollection = CFₘ ⟅ PreThingCollectionCollection ⟆

  PreThingSingleton : obₘ
  PreThingSingleton = PreThingCollection

  PreThingSingletonCollection : obₘ
  PreThingSingletonCollection = CFₘ ⟅ PreThingSingleton ⟆

  PreInteraction : obₘ
  PreInteraction = PreThingCollection
```
Note that `PrePlace` is directly defined as `prePlaceFunctor ⟅ Uᵥ ⟆` while
`PreThingCollection` is indirectly defined as `CFₘ ⟅ PreThing ⟆.`

`Pₘ` is the ambient parameter representing *atomic pre-things*, whereas
`PreThingCollection` represents *composite pre-things*. The morphism
`potentialAsPreThingMorphism` structurally converts atomic potentials into generic
pre-things, while `preThingCollectionAsPreThingMorphism` converts composite
pre-thing-collections into generic pre-things.

`PreInteraction` formalizes a pre-thing-collection of *interacting* pre-things. Not all
pre-thing-collection consist of interacting pre-things.

#### `Type` typed

```agda
  UniverseTransition : Type m
  UniverseTransition = Cᵥ [ Uᵥ , Uᵥ ]

  PrePlaceTransitionMapping : Type (ℓ-max o m)
  PrePlaceTransitionMapping = TransitionMapping Cᵥ prePlaceFunctor

  PrePlaceTransition : Type m
  PrePlaceTransition = Cᵥ [ PrePlace , PrePlace ]

  PreThingCollectionTransition : Type m
  PreThingCollectionTransition =
    Cₘ [ PreThingCollection , PreThingCollection ]

  PreThingCollectionFunctorTransition : Type m
  PreThingCollectionFunctorTransition =
    Cₘ [ preThingCollectionFunctor ⟅ Uᵥ ⟆ , preThingCollectionFunctor ⟅ Uᵥ ⟆ ]

  PreThingCollectionCollectionTransition : Type m
  PreThingCollectionCollectionTransition =
    Cₘ [ PreThingCollectionCollection , PreThingCollectionCollection ]

  PreThingCollectionPrePlaceHeteroMorphism : Type m
  PreThingCollectionPrePlaceHeteroMorphism = Het[ PreThingCollection , PrePlace ]

  PreThingSingletonCollectionPrePlaceCollectionHeteromorphism : Type m
  PreThingSingletonCollectionPrePlaceCollectionHeteromorphism =
    Het[ PreThingSingletonCollection , PrePlaceCollection ]
```

#### Global Elements and Global Hetero-Elements

```agda
  GlobalPreThingCollection : Type m
  GlobalPreThingCollection = GlobalElement CWTₘ PreThingCollection

  GlobalPreInteraction : Type m
  GlobalPreInteraction = GlobalElement CWTₘ PreInteraction

  GlobalPreThingCollectionCollection : Type m
  GlobalPreThingCollectionCollection =
    GlobalElement CWTₘ PreThingCollectionCollection

  GlobalHeteroElement : obᵥ → Type m
  GlobalHeteroElement Z = Het[ 1ₘ , Z ]

  GlobalHeteroPrePlace : Type m
  GlobalHeteroPrePlace = GlobalHeteroElement PrePlace
```
#### `transformationMorphism` related

We evaluate the four natural transformations (η, μ, ζ, χ) at object `PreThing` to
produce four generic morphisms/transitions of the material universe.

Notice the syntactic difference in how instances are passed:

- `IsMonad` comes from the external `Cubical.Categories.Monad.Base` library, where
  `open IsMonad` declares `η` and `μ` with an *explicit* record parameter:
  `η : IsMonad M → NatTrans Id M`. Hence, we pass `materialCollectionIsMonad` in round
  parentheses: `(η materialCollectionIsMonad)`.

- In contrast, our own `record Zero` and `record Choices` were opened using Agda instance
  syntax: `open Zero {{...}} public` and `open Choices {{...}} public`. Their projections
  `ζ` and `χ` expect *instance arguments* `{{...}}`. To assist Agda's type inference and
  prevent unsolved metas when resolving the ambient category and functor, we pass the
  instance explicitly using double brackets: `⦃ materialCollectionZero ⦄`.

```agda
  singletonTransformationMorphism : 
    Cₘ [ PreThing , PreThingSingleton ]
  singletonTransformationMorphism =
    transformationMorphism (η materialCollectionIsMonad) PreThing

  unionTransformationMorphism :
    Cₘ [ PreThingCollectionCollection , PreThingCollection ]
  unionTransformationMorphism =
    transformationMorphism (μ materialCollectionIsMonad) PreThing

  zeroTransformationTransition : PreThingCollectionTransition
  zeroTransformationTransition =
    transformationMorphism (ζ ⦃ materialCollectionZero ⦄) PreThing

  choicesTransformationTransition : PreThingCollectionCollectionTransition
  choicesTransformationTransition =
    transformationMorphism (χ ⦃ materialCollectionChoices ⦄) PreThing
```

#### `CFₘ` nesting related

```agda
  nestedSingletonTransformationMorphism :
    Cₘ [ PreThingCollection , PreThingCollectionCollection ]
  nestedSingletonTransformationMorphism = CFₘ ⟪ singletonTransformationMorphism ⟫

  doubleNestedSingletonTransformationMorphism :
    Cₘ
      [ PreThingCollectionCollection , PreThingCollectionCollectionCollection ]
  doubleNestedSingletonTransformationMorphism =
    CFₘ ⟪ nestedSingletonTransformationMorphism ⟫

  nestedUnionTransformationMorphism :
    Cₘ [ PreThingCollectionCollectionCollection , PreThingCollectionCollection ]
  nestedUnionTransformationMorphism = CFₘ ⟪ unionTransformationMorphism ⟫
```

### Various `field` declarations

#### `preThingCollectionPathEquality`

Recall that in the virtual universe, `PrePlace` is defined as:

- `PrePlace = prePlaceFunctor ⟅ Uᵥ ⟆`

where `Uᵥ` is a designated virtual universe object representing the
underlying state (or time) of the virtual universe. Consequently, `PrePlace` is
equal to `prePlaceFunctor ⟅ Uᵥ ⟆` by **definitional equality**.

Similarly, in the material universe, we define:

- `PreThingCollection = CFₘ ⟅ PreThing ⟆`

However, the connection between the virtual state `Uᵥ` and the material
collection `PreThingCollection` is governed by the cross-universe functor
`preThingCollectionFunctor : Functor Cᵥ Cₘ`
as `preThingCollectionFunctor ⟅ Uᵥ ⟆`. Its equality with `PreThingCollection` is
not definitional; instead, it is formally declared by a **path equality**:

```agda
  field
    preThingCollectionPathEquality :
      preThingCollectionFunctor ⟅ Uᵥ ⟆ ≡ PreThingCollection
```

A path equality `z ≡ y` is a function `p : I → Z` from an abstract interval `I`,
satisfying endpoint conditions `p(i0) = z` and `p(i1) = y`.

Operations like `transport` and path composition `_∙_` compute directly
without needing unproven postulates.

Type equivalence `(Z ≃ Y)` asserts that two property types — such as a proposition and a
path equality equation — are computationally equivalent without resorting to classical axioms.

Through Univalence (`ua`), any such equivalence `(Z ≃ Y)` of type `Type lzero` can be
converted into a path equality `(Z ≡ Y)`.

#### `isGlobalPreThingSingleton` and `isGlobalPreInteraction` predicates

Below we declare two predicate-like `field`s stating being able to distinguish global
elements of a pre-thing-singleton and a pre-interaction from other global elements of a
pre-thing-collection. The former is purely structural; the latter reflects whether all
pre-things in the collection interact.

```agda
    isGlobalPreThingSingleton :
      GlobalPreThingCollection → Type m

    isGlobalPreInteraction :
      GlobalPreThingCollection → Type m
```

#### `preThingCollectionAsPreThingMorphism` structural conversion proposition

Below we declare a pure structural `field` stating the ability to morph pre-thing-collections
to pre-things.

```agda
    preThingCollectionAsPreThingMorphism :
      Cₘ [ PreThingCollection , PreThing ]
```

#### `preThingCollectionAsPreInteractionMorphism` conversion proposition

Below we declare a conversion `field` stating the ability to morph pre-thing-collections to
pre-interactions (of course assuming `isGlobalPreInteraction` above).

```agda
    preThingCollectionAsPreInteractionMorphism :
      Cₘ [ PreThingCollection , PreInteraction ]
```

#### `preThingCollectionPrePlaceHeteroMorphism` formalizing pre-thing-collection--pre-place

Below we formalize *pre-thing-collection--pre-place* by declaring it as a heteromorphism.

Pre-thing-collection transitions act upon this pre-thing-collection--pre-place
heteromorphism and pre-place transitions act upon this pre-thing-collection--pre-place
heteromorphism as well.


```agda
    preThingCollectionPrePlaceHeteroMorphism :
      PreThingCollectionPrePlaceHeteroMorphism
```

#### `preThingSingletonPrePlaceHeteroMorphismLift` singleton Mapping

Below we formalize the ability to lift a pre-thing-collection--pre-place to a
pre-thing-singleton-collection--pre-place-collection.


```agda
    preThingSingletonPrePlaceHeteroMorphismLift :
      PreThingCollectionPrePlaceHeteroMorphism →
        PreThingSingletonCollectionPrePlaceCollectionHeteromorphism
```

#### `ProsetStr` `instance` declarations

Below we formalize `ProsetStr` `instance` definitions, one for transitions, two for morphisms
and one for heteromorphisms.

```agda
    instance
      universeTransitionProsetStr :
        ProsetStr m UniverseTransition

      globalPreThingCollectionProsetStr :
        ProsetStr m GlobalPreThingCollection

      globalHeteroPrePlaceProsetStr :
        ProsetStr m GlobalHeteroPrePlace

      prePlaceMorphismSupremum :
        Supremum Cᵥ CFᵥ PrePlace
```

### Various definitions

#### `universeTransitionToPrePlaceTransition`

`universeTransitionToPrePlaceTransition` uses `prePlaceFunctor` at morphism level.

```agda
  universeTransitionToPrePlaceTransition :
    UniverseTransition → PrePlaceTransition
  universeTransitionToPrePlaceTransition universeTransition =
    prePlaceFunctor ⟪ universeTransition ⟫
```

#### `universeTransitionToPreThingCollectionFunctorTransition`

`universeTransitionToPreThingCollectionFunctorTransition` uses
`preThingCollectionFunctor` at morphism level.

```agda
  universeTransitionToPreThingCollectionFunctorTransition :
    UniverseTransition → PreThingCollectionFunctorTransition
  universeTransitionToPreThingCollectionFunctorTransition =
    λ universeTransition →
      preThingCollectionFunctor ⟪ universeTransition ⟫
```

### `preThingCollectionTransitionPathEquality`

Recall the definitional structure of transition types:

- `PrePlaceTransition` is definitionally equal to
  `Cᵥ [ PrePlace , PrePlace ]`.

- `PreThingCollectionTransition` is definitionally equal to
  `Cₘ [ PreThingCollection , PreThingCollection ]`.

- `PreThingCollectionFunctorTransition` is definitionally equal to
  `Cₘ [`
  `  preThingCollectionFunctor ⟅ Uᵥ ⟆`
  `, preThingCollectionFunctor ⟅ Uᵥ ⟆ ]`.

Here we witness the striking harmony between **Category Theory transitions** and
**Homotopy Type Theory paths**:

- In Category Theory, universe entities evolve *at* transitions (endomorphisms).

- In Homotopy Type Theory, equalities are continuous *paths* along which terms
  can be *transported*.

While `preThingCollectionPathEquality` gives us a path equality between *objects*
(`Z ≡ Y`), we need a path equality between their *transition types* (`[ Z , Z ] ≡ [ Y , Y ]`)
in order to transport endomorphisms.

To accomplish this, we define the *path equality lifter*
`materialTransitionPathEqualityLifter`. Given any path equality `z≡y : Z ≡ Y` between
material objects, it maps each point of the interval `i : I` to the endomorphism hom-type
`Cₘ [ z≡y i , z≡y i ]`:

```agda
  materialTransitionPathEqualityLifter :
    {Z Y : obₘ} → Z ≡ Y → Cₘ [ Z , Z ] ≡ Cₘ [ Y , Y ]
  materialTransitionPathEqualityLifter z≡y =
    λ i → Cₘ [ z≡y i , z≡y i ]
```

The `preThingCollectionTransitionPathEquality` type is a transition version of
the `preThingCollectionPathEquality` type that is lifted using
`materialTransitionPathEqualityLifter`.

```agda
  preThingCollectionTransitionPathEquality :
    PreThingCollectionFunctorTransition ≡ PreThingCollectionTransition
  preThingCollectionTransitionPathEquality =
    materialTransitionPathEqualityLifter preThingCollectionPathEquality
```

#### `universeTransitionToPreThingCollectionTransition`

With `preThingCollectionTransitionPathEquality` in hand, we can now define how a
virtual universe transition induces a material pre-thing-collection transition:

1. First, we apply the functor `preThingCollectionFunctor` at the morphism level
   to obtain a transition on the functor image:
   `preThingCollectionFunctor ⟪ universeTransition ⟫`.

2. Second, we **`transport`** this functorial transition along the lifted path equality
   `preThingCollectionTransitionPathEquality` directly into a `PreThingCollectionTransition`:

```agda
  universeTransitionToPreThingCollectionTransition :
     UniverseTransition → PreThingCollectionTransition
  universeTransitionToPreThingCollectionTransition =
    λ universeTransition →
      let preThingCollectionFunctorTransition =
            universeTransitionToPreThingCollectionFunctorTransition universeTransition
          preThingCollectionTransition =
            transport
              preThingCollectionTransitionPathEquality
              preThingCollectionFunctorTransition
      in preThingCollectionTransition
```

In this way, Homotopy Type Theory path equality transport and Category Theory transitions
operate in complete synthesis: dynamic state evolution in the virtual universe transports
natively into dynamic evolution of material universe pre-thing-collections.

#### `preThingCollectionCollectionAsPreThingCollectionMorphism` conversion morphism

```agda
  preThingCollectionCollectionAsPreThingCollectionMorphism :
    Cₘ [ PreThingCollectionCollection , PreThingCollection ]
  preThingCollectionCollectionAsPreThingCollectionMorphism =
    CFₘ ⟪ preThingCollectionAsPreThingMorphism ⟫
```

#### `preThingCollectionCollectionAsPreInteractionMorphism` conversion morphism

```agda
  preThingCollectionCollectionAsPreInteractionMorphism :
    Cₘ [ PreThingCollectionCollection , PreInteraction ]
  preThingCollectionCollectionAsPreInteractionMorphism =
    preThingCollectionCollectionAsPreThingCollectionMorphism ⋙ₘ
      preThingCollectionAsPreInteractionMorphism
```

#### `isGlobalPreThingSingletonInteraction` predicate

```agda
  isGlobalPreThingSingletonInteraction :
    GlobalPreThingCollection → Type m
  isGlobalPreThingSingletonInteraction globalPreThingCollection =
    isGlobalPreThingSingleton globalPreThingCollection ×
      isGlobalPreInteraction globalPreThingCollection
```

## Various property definitions

### Movement related

`_isMovementAtUniverseTransition_` is a pointfree movement property stating that a
 "movement (pre-place transition)" acting upon a "pre-thing-collection transition"
 acting upon a "pre-thing collection--pre-place" equals a corresponding
 "pre-place transition" acting upon that "pre-thing-collection--pre-place".

Various derived movement related properties are defined as well.

```agda
  _isMovementAtUniverseTransition_ :
    PrePlaceTransitionMapping → UniverseTransition → Type m
  _isMovementAtUniverseTransition_ prePlaceTransitionMapping universeTransition =
    let prePlaceTransition =
          universeTransitionToPrePlaceTransition
            universeTransition
        preThingCollectionTransition =
          universeTransitionToPreThingCollectionTransition
            universeTransition
        movement =
          transitionMapping prePlaceTransitionMapping universeTransition
    in (preThingCollectionTransition ⋆L preThingCollectionPrePlaceHeteroMorphism) ⋆R movement ≡
       (preThingCollectionPrePlaceHeteroMorphism ⋆R prePlaceTransition)

  isImmobileAtUniverseTransition : UniverseTransition → Type m
  isImmobileAtUniverseTransition universeTransition =
    (idTransitionMapping Cᵥ prePlaceFunctor)
      isMovementAtUniverseTransition
        universeTransition

  _isMovement_ : PrePlaceTransitionMapping → Type m
  _isMovement_ prePlaceTransitionMapping =
    ∀ (universeTransition : UniverseTransition) →
      prePlaceTransitionMapping isMovementAtUniverseTransition universeTransition

  isImmobile : Type m
  isImmobile =
    ∀ (universeTransition : UniverseTransition) →
      isImmobileAtUniverseTransition universeTransition

  _isUniformMovementAtUniverseTransition_ :
    PrePlaceTransitionMapping → UniverseTransition → Type m
  _isUniformMovementAtUniverseTransition_ prePlaceTransitionMapping universeTransition =
    ∀ (subUniverseTransition : UniverseTransition) →
      subUniverseTransition ≲ universeTransition →
        prePlaceTransitionMapping isMovementAtUniverseTransition subUniverseTransition

  isUniformlyImmobileAtUniverseTransition : UniverseTransition → Type m
  isUniformlyImmobileAtUniverseTransition universeTransition =
    ∀ (subUniverseTransition : UniverseTransition) →
      subUniverseTransition ≲ universeTransition →
        isImmobileAtUniverseTransition subUniverseTransition

  isUniformMovement : PrePlaceTransitionMapping → Type m
  isUniformMovement prePlaceTransitionMapping =
    ∀ (universeTransition : UniverseTransition) →
     prePlaceTransitionMapping isUniformMovementAtUniverseTransition universeTransition

  isUniformImmobile : Type m
  isUniformImmobile =
    ∀ (universeTransition : UniverseTransition) →
      isUniformlyImmobileAtUniverseTransition universeTransition
```

### `zeroTransitionAbsorption` -- done

`zeroTransitionAbsorption`, a proof that zero transitions absorb material
universe pre-thing-collection transitions, is defined as an instance of `zero-absorption`.

```agda
  ZeroTransitionAbsorption : Type m
  ZeroTransitionAbsorption =
    ∀ (universeTransition : UniverseTransition) →
      let preThingCollectionTransition =
            universeTransitionToPreThingCollectionTransition
              universeTransition
      in zeroTransformationTransition ⋙ₘ preThingCollectionTransition ≡
           zeroTransformationTransition

  zeroTransitionAbsorption : ZeroTransitionAbsorption
  zeroTransitionAbsorption =
    λ universeTransition →
      let preThingCollectionTransition =
            universeTransitionToPreThingCollectionTransition
              universeTransition
      in zero-absorption preThingCollectionTransition
```

### `choicesToPreThingCollectionCollectionUnionAbsorption`

`choicesToPreThingCollectionCollectionUnionAbsorption` is a proof that union transitions
absorb material universe pre-thing-collection choices transitions, is defined as
`choices-union-absorption`.

```agda
  ChoicesToPreThingCollectionCollectionUnionAbsorption : Type m
  ChoicesToPreThingCollectionCollectionUnionAbsorption =
    (choicesTransformationTransition ⋙ₘ unionTransformationMorphism) ≡
      unionTransformationMorphism

  choicesToPreThingCollectionCollectionUnionAbsorption :
    ChoicesToPreThingCollectionCollectionUnionAbsorption
  choicesToPreThingCollectionCollectionUnionAbsorption = choices-union-absorption
```

### `preThingCollectionIsPreInteractionPreservation` -- done

```agda
  preThingCollectionIsPreInteractionPreservation : Type m
  preThingCollectionIsPreInteractionPreservation =
    ∀ (universeTransition : UniverseTransition) →
      let preThingCollectionTransition =
            universeTransitionToPreThingCollectionTransition
              universeTransition
      in
        (globalPreThingCollection : GlobalPreThingCollection) →
          isGlobalPreInteraction globalPreThingCollection 
      → isGlobalPreInteraction
         (globalPreThingCollection ⋙ₘ preThingCollectionTransition)
```

### `isGlobalPreThingSingletonEquivalence` and Path Equality Variant

In constructive Homotopy Type Theory, properties can be formalized in two complementary,
univalently equivalent ways at different type universe levels:

1. **Structural Type Equivalence (`_≃_`)**:
   at type universe level `Type m`

2. **Path Equality (`_≡_`)**:
   at type universe level `Type (lsuc m)`

The **Univalence Principle** (`univalence : (A ≡ B) ≃ (A ≃ B)`) states that type
equivalence and path equality are themselves equivalent. In `Cubical Agda`, univalence
computes natively via two inverse operations:

- `ua : A ≃ B → A ≡ B` (lifts an equivalence into a path equality).

- `pathToEquiv : A ≡ B → A ≃ B` (extracts the equivalence from a path equality).

Below we illustrate this.

```agda
  isGlobalPreThingSingletonEquivalence : Type m
  isGlobalPreThingSingletonEquivalence =
    (globalPreThingCollection : GlobalPreThingCollection)
    → isGlobalPreThingSingleton globalPreThingCollection ≃
        (globalPreThingCollection ⋙ₘ
          preThingCollectionAsPreThingMorphism ⋙ₘ
            singletonTransformationMorphism ≡
              globalPreThingCollection)

  isGlobalPreThingSingletonPathEquality : Type (lsuc m)
  isGlobalPreThingSingletonPathEquality =
    (globalPreThingCollection : GlobalPreThingCollection)
    → isGlobalPreThingSingleton globalPreThingCollection ≡
        (globalPreThingCollection ⋙ₘ
          preThingCollectionAsPreThingMorphism ⋙ₘ
            singletonTransformationMorphism ≡
              globalPreThingCollection)

  equivalenceToPathEquality :
    isGlobalPreThingSingletonEquivalence →
      isGlobalPreThingSingletonPathEquality
  equivalenceToPathEquality proofEquiv =
    λ globalPreThingCollection →
      ua (proofEquiv globalPreThingCollection)

  pathEqualityToEquivalence :
    isGlobalPreThingSingletonPathEquality →
      isGlobalPreThingSingletonEquivalence
  pathEqualityToEquivalence proofPath =
    λ globalPreThingCollection →
      pathToEquiv (proofPath globalPreThingCollection)

  isGlobalPreThingSingletonPathEquality' :
    isGlobalPreThingSingletonEquivalence →
      isGlobalPreThingSingletonPathEquality
  isGlobalPreThingSingletonPathEquality' = equivalenceToPathEquality

  isGlobalPreThingSingletonEquivalence' :
    isGlobalPreThingSingletonPathEquality →
      isGlobalPreThingSingletonEquivalence
  isGlobalPreThingSingletonEquivalence' = pathEqualityToEquivalence
```

Above, we defined two formulations and demonstrated how univalence bridges them:

1. **Structural Type Equivalence (`_≃_`)**:
   Expresses that the predicate `isGlobalPreThingSingleton f` and the
   equation `(f ⋙ₘ ...) ≡ f` are in 1-to-1 correspondence.
   This formulation lives at universe level `Type m`.

2. **Path Equality (`_≡_`)**:
   Expresses that the predicate and the idempotence equation are *literally identical types*
   along a path over an interval dimension.
   Because it asserts an equality between types, it lives one universe level higher:
   `Type (lsuc m)`.

Below are a few extra univalence related definitions, one using `invEquiv`, and one using
`iso`, `isoToEquiv`, `ua-pathToEquiv` and `pathToEquiv-ua`.

```agda
  globalPreThingSingletonEquivToPathEquiv :
    (globalPreThingCollection : GlobalPreThingCollection)
    → (isGlobalPreThingSingleton globalPreThingCollection ≃
        ((globalPreThingCollection ⋙ₘ
          preThingCollectionAsPreThingMorphism ⋙ₘ
            singletonTransformationMorphism) ≡
              globalPreThingCollection)) ≃
      (isGlobalPreThingSingleton globalPreThingCollection ≡
        ((globalPreThingCollection ⋙ₘ
          preThingCollectionAsPreThingMorphism ⋙ₘ
            singletonTransformationMorphism) ≡
              globalPreThingCollection))
  globalPreThingSingletonEquivToPathEquiv _ = invEquiv univalence

  isGlobalPreThingSingletonEquivalenceProofEquivPathEqualityProof :
    isGlobalPreThingSingletonEquivalence ≃
      isGlobalPreThingSingletonPathEquality
  isGlobalPreThingSingletonEquivalenceProofEquivPathEqualityProof =
    isoToEquiv (iso equivalenceToPathEquality pathEqualityToEquivalence
      (λ proofPath → λ i f → ua-pathToEquiv (proofPath f) i)
      (λ proofEquiv → λ i f → pathToEquiv-ua (proofEquiv f) i))
```

To summarize:

- *`_≃_` (Equivalence)*: Expresses that the two property types are in 1-to-1
  correspondence (type equivalence) within `Type m`.

- *`_≡_` (Path Equality)*: Expresses that the two property types are *literally
  the same path-equal type* in the higher universe `Type (lsuc m)`.

- *`ua` & `pathToEquiv`*: Natively convert back and forth between equivalence and
  path equality proofs.

Moreover:

- *`isoToEquiv`*: Proves that the type of equivalence proofs and the type of path
  equality proofs are themselves univalently equivalent!


### `preThingCollectionToPrePlacePreOrderPreservation`

Both `GlobalPreThingCollection`s and `GlobalHeteroPrePlace` are
`ProsetStr` instances. 

```agda
  preThingCollectionToPrePlacePreOrderPreservation : Type m
  preThingCollectionToPrePlacePreOrderPreservation =
    (leftGlobalPreThingCollection rightGlobalPreThingCollection :
      GlobalPreThingCollection) →
        leftGlobalPreThingCollection ≲ rightGlobalPreThingCollection →
        let leftGlobalHeteroPrePlace = 
              leftGlobalPreThingCollection ⋆L
                preThingCollectionPrePlaceHeteroMorphism
            rightGlobalHeteroPrePlace = 
              rightGlobalPreThingCollection ⋆L
                preThingCollectionPrePlaceHeteroMorphism
        in leftGlobalHeteroPrePlace ≲ rightGlobalHeteroPrePlace
```

### `prePlaceOfPreThingCollectionAsSupremumMorphismOfAllPrePlacesOfAllSingletons`

The property below states that a pre-thing-collection to pre-place heteromorphism is
defined by the supremum of its pre-thing-singleton-collection to pre-place-collection
heteromorphism.

```agda
  prePlaceOfPreThingCollectionAsSupremumMorphismOfAllPrePlacesOfAllSingletons : Type m
  prePlaceOfPreThingCollectionAsSupremumMorphismOfAllPrePlacesOfAllSingletons =
    let -- preThingSingletonCollectionPrePlaceCollectionHeteroMorphism :
          -- Het[ PreThingSingletonCollection , PrePlaceCollection ]
        preThingSingletonCollectionPrePlaceCollectionHeteroMorphism =
          preThingSingletonPrePlaceHeteroMorphismLift
             preThingCollectionPrePlaceHeteroMorphism
        -- preThingCollectionPrePlaceHeteroMorphism' :
          -- Het[ PreThingCollection , PrePlace ]
        preThingCollectionPrePlaceHeteroMorphism' =
          (nestedSingletonTransformationMorphism ⋆L
            preThingSingletonCollectionPrePlaceCollectionHeteroMorphism) ⋆R supremum
    in preThingCollectionPrePlaceHeteroMorphism ≡ preThingCollectionPrePlaceHeteroMorphism'
```

### `preInteractionCollectionAsUnionOfSingletonsOfChoicesPreInteraction`

The property below states, in a pointfree way, that, if a pre-thing-collection-collection 
, seen as a pre-thing-collection, is a pre-interaction, in other words, if its
pre-thing-collections interact, then it can be seen as the union of the
double-nested singleton pre-interactions of all choices of pre-things in all
pre-thing-collections seen as a pre-interaction.

```agda
  preInteractionCollectionAsUnionOfSingletonsOfChoicesPreInteraction : Type m
  preInteractionCollectionAsUnionOfSingletonsOfChoicesPreInteraction =
    (globalPreThingCollectionCollection :
      GlobalPreThingCollectionCollection)
    → let globalPreThingCollection =
            globalPreThingCollectionCollection ⋙ₘ
              preThingCollectionCollectionAsPreThingCollectionMorphism
          globalPreInteraction =
            globalPreThingCollection ⋙ₘ
              preThingCollectionAsPreInteractionMorphism
          globalPreInteraction' =
            globalPreThingCollectionCollection ⋙ₘ
              choicesTransformationTransition ⋙ₘ
                doubleNestedSingletonTransformationMorphism ⋙ₘ
                  nestedUnionTransformationMorphism ⋙ₘ
                    preThingCollectionCollectionAsPreInteractionMorphism
      in isGlobalPreInteraction globalPreThingCollection →
          globalPreInteraction ≡ globalPreInteraction'
```

### Discrete Intervals, Homotopy Levels, and Concrete Sets

To formalize durations as transition intervals equipped with `start` and `end` boundary
elements, and to prove that the resulting interval preorder satisfies proset properties
(transitivity and proposition-valuedness), we import:
- Homotopy levels (`isPropΠ`, `isPropΠ2`, `isProp→`, `isProp×`, `isSet×`, `isSetRetract`)
  from `Cubical.Foundations.HLevels`.
- The category of sets `SET` from `Cubical.Categories.Instances.Sets` (for the concrete
  material pre-thing object in `PreOrderedReality`).

```agda
open import Cubical.Foundations.HLevels
  using (isPropΠ; isPropΠ2; isProp→; isProp×; isSet×; isSetRetract)
open import Cubical.Categories.Instances.Sets using (SET)
```

### `record TransitionInterval`

A time interval `record TransitionInterval` models a duration of time as an
interval-like transition equipped with a `start` and an `end` boundary state.

```agda
record TransitionInterval
    {o m : Level}
    (C : CategoryWithTerminal o m)
    (Z : Category.ob (CategoryWithTerminal.category C))
    {{_ : ProsetStr m (GlobalElement C Z)}} : Type (ℓ-max o m) where
  field
    transition : CategoryWithTerminal.category C [ Z , Z ]
    start      : GlobalElement C Z
    end        : GlobalElement C Z

open TransitionInterval public

instance
  transitionIntervalProsetStr :
    ∀ {o m} {C : CategoryWithTerminal o m} {Z}
      {{elementProsetStr : ProsetStr m (GlobalElement C Z)}} →
      ProsetStr m (TransitionInterval C Z)
  transitionIntervalProsetStr
    {m = m} {C = C} {Z = Z} {{elementProsetStr = elementProsetStr}} =
    prosetstr _≲TI_ isProsetTI
    where
    open CategoryWithTerminal C renaming (_∘_ to _∘C_; isSetHom to isSetHomC)
    elementIsProset = ProsetStr.isProset elementProsetStr

    _≲TI_ : TransitionInterval C Z → TransitionInterval C Z → Type m
    ti1 ≲TI ti2 =
      (start ti2 ≲ start ti1) ×
      (end ti1 ≲ end ti2)

    isSetTI : isSet (TransitionInterval C Z)
    isSetTI =
      isSetRetract
        (λ int → transition int , start int , end int)
        (λ (t , s , e) → record { transition = t ; start = s ; end = e })
        (λ _ → refl)
        (isSet× isSetHomC (isSet× isSetHomC isSetHomC))

    isProsetTI : IsProset _≲TI_
    IsProset.is-set isProsetTI =
      isSetTI
    IsProset.is-prop-valued isProsetTI ti1 ti2 =
      isProp× (IsProset.is-prop-valued elementIsProset _ _)
              (IsProset.is-prop-valued elementIsProset _ _)
    IsProset.is-refl isProsetTI int =
      IsProset.is-refl elementIsProset (start int) ,
      IsProset.is-refl elementIsProset (end int)
    IsProset.is-trans isProsetTI ti1 ti2 int ≤12 ≤23 =
      IsProset.is-trans elementIsProset _ _ _ (≤23 .fst) (≤12 .fst) ,
      IsProset.is-trans elementIsProset _ _ _ (≤12 .snd) (≤23 .snd)
```

### `record Gap`

A `record Gap` models a temporal separation or hiatus between manifestation sequences,
bounded by a `start` and an `end` global state element out of the terminal object.

```agda
record Gap
    {o m : Level}
    (C : CategoryWithTerminal o m)
    (Z : Category.ob (CategoryWithTerminal.category C))
    {{_ : ProsetStr m (GlobalElement C Z)}} : Type (ℓ-max o m) where
  field
    start : GlobalElement C Z
    end   : GlobalElement C Z

open Gap public

TerminalSET : ∀ {ℓ} → Terminal (SET ℓ)
TerminalSET .fst = Unit* , isSetUnit*
TerminalSET .snd Y .fst _ = tt*
TerminalSET .snd Y .snd f = funExt (λ z → isPropUnit* tt* (f z))

SETWithTerminal : ∀ ℓ → CategoryWithTerminal (lsuc ℓ) ℓ
SETWithTerminal ℓ .CategoryWithTerminal.category = SET ℓ
SETWithTerminal ℓ .CategoryWithTerminal.T = TerminalSET
```

### `record PreOrderedReality`

`record PreOrderedReality` formalizes Fred Van Oystaeyen's requirement that time /
global state elements in `Cᵥ [ 1ᵥ , Uᵥ ]` are preordered
(`ProsetStr`).

Inside `PreOrderedReality`, manifestations, connected chains of manifestations,
disconnected manifestation sequences (with intervening gaps), and observations are defined:

- A **Manifestation** models the realization of a material thing (`PreThing .fst`)
  over a virtual universe transition interval (`VirtualUniverseTransitionInterval`).
- **ConnectedManifestations**: A non-empty chain of consecutive manifestations
  without temporal gaps, where consecutive manifestations satisfy `m1 isConsecutiveTo m2`.
- **DisconnectedManifestations**: Sequences of connected manifestation chains
  interspersed with explicit `Gap` intervals, where boundary path equalities ensure exact
  continuity across gaps.
- **Observation**: An observation over a duration `observationInterval` encompassing
  a sequence of manifestations subject to the boundary constraint `observationConstraint`.

```agda
record PreOrderedReality
    {ℓ : Level}
    (CWTᵥ : CategoryWithTerminal (lsuc ℓ) ℓ)
    (CFᵥ : Functor (CategoryWithTerminal.category CWTᵥ)
                   (CategoryWithTerminal.category CWTᵥ))
    (CFₘ : Functor (SET ℓ) (SET ℓ))
    (PFₘᵥ : Profunctor⊶ (lsuc ℓ) ℓ (SET ℓ) (CategoryWithTerminal.category CWTᵥ))
    (Uᵥ : Category.ob (CategoryWithTerminal.category CWTᵥ))
    (Pₘ : Category.ob (SET ℓ)) :
      Type (lsuc (lsuc ℓ)) where

  open CategoryWithTerminal CWTᵥ
    renaming
      ( category to Cᵥ
      ; ob to obᵥ
      ; id to idᵥ
      ; _∘_ to _∘ᵥ_
      ; isSetHom to isSetHomᵥ
      ; 1C to 1ᵥ
      ; T to Tᵥ
      )

  field
    reality :
      Reality Cᵥ (SETWithTerminal ℓ) CFᵥ CFₘ PFₘᵥ Uᵥ Pₘ

    instance
      virtualUniverseGlobalElementProsetStr :
        ProsetStr ℓ (GlobalElement CWTᵥ Uᵥ)

    virtualUniverseElement :
      GlobalElement CWTᵥ Uᵥ

  open Reality reality public

  VirtualUniverseTransitionInterval = TransitionInterval CWTᵥ Uᵥ

  record Manifestation : Type (lsuc ℓ) where
    field
      thing : PreThing .fst
      manifestationInterval : VirtualUniverseTransitionInterval

  open Manifestation public

  _isConsecutiveTo_ : Manifestation → Manifestation → Type ℓ
  m1 isConsecutiveTo m2 = end (manifestationInterval m1) ≡ start (manifestationInterval m2)

  data ConnectedManifestations : Type (lsuc ℓ)

  firstM : ConnectedManifestations → Manifestation

  data ConnectedManifestations where
    ⟦_⟧ : Manifestation → ConnectedManifestations
    _∷M[_]_ :
      (m : Manifestation) →
      (ms : ConnectedManifestations) →
      (m isConsecutiveTo (firstM ms)) →
        ConnectedManifestations

  pattern oneM m = ⟦ m ⟧
  pattern consM ms m p = _∷M[_]_ m p ms
  pattern _∷M_ ms m = _∷M[_]_ m _ ms

  infixr 5 _∷M[_]_ _∷M_ consM

  firstM ⟦ m ⟧ = m
  firstM (_∷M[_]_ m _ _) = m

  lastM : ConnectedManifestations → Manifestation
  lastM ⟦ m ⟧ = m
  lastM (_∷M[_]_ _ ms _) = lastM ms

  data DisconnectedManifestations : Type (lsuc ℓ)

  firstCMS : DisconnectedManifestations → ConnectedManifestations

  data DisconnectedManifestations where
    ⟦⟦_⟧⟧ : ConnectedManifestations → DisconnectedManifestations
    _::G[_]_ :
      (cms : ConnectedManifestations) →
      (gap : Gap CWTᵥ Uᵥ) →
      (dms : DisconnectedManifestations) →
      {p1 : end (manifestationInterval (lastM cms)) ≡ Gap.start gap} →
      {p2 : Gap.end gap ≡ start (manifestationInterval (firstM (firstCMS dms)))} →
        DisconnectedManifestations

  pattern oneDM cms = ⟦⟦ cms ⟧⟧
  pattern consDM cms gap dms p1 p2 = _::G[_]_ cms gap dms {p1} {p2}

  infixr 4 _::G[_]_ consDM

  firstCMS ⟦⟦ cms ⟧⟧ = cms
  firstCMS (_::G[_]_ cms _ _) = cms

  lastCMS : DisconnectedManifestations → ConnectedManifestations
  lastCMS ⟦⟦ cms ⟧⟧ = cms
  lastCMS (_::G[_]_ _ _ dms) = lastCMS dms

  StartE : DisconnectedManifestations → GlobalElement CWTᵥ Uᵥ
  StartE dms = start (manifestationInterval (firstM (firstCMS dms)))

  endE : DisconnectedManifestations → GlobalElement CWTᵥ Uᵥ
  endE dms = end (manifestationInterval (lastM (lastCMS dms)))

  record Observation : Type (lsuc ℓ) where
    field
      observationInterval : VirtualUniverseTransitionInterval
      disconnectedManifestations : DisconnectedManifestations
      observationConstraint :
          StartE disconnectedManifestations ≲ start observationInterval
        × end observationInterval ≲ endE disconnectedManifestations
```
## MaterialUniverse as Category of Sets and Functions (`SET₀`)

We formalize the material universe concretely as the category of sets and functions
`SET₀ = SET lzero`, equipped with the **Kuratowski Finite Sets** monad (`LFSet`)
from `Cubical.HITs.ListedFiniteSet`.

- **Collection Functor**: `LFSetFunctor` maps each set `(A, isSetA)` to
  `(LFSet A, trunc)`, preserving universe levels.
- **Monad Multiplication**: `flattenLFSet` flattens nested finite sets via set
  union (`_++_`).
- **Choices**: Choices natural transformation satisfies union absorption
  `union ∘ χ ≡ union`.
- **Preorder on Morphisms**: Preorder on morphisms to pre-things is given by
  pointwise subset inclusion `f ≲ g ⇔ ∀ z x, x ∈ f(z) ⇒ x ∈ g(z)`.

```agda
-- MaterialUniverse Implementation: SET₀ with LFSet
--------------------------------------------------------------------------------

open import Cubical.HITs.ListedFiniteSet.Base as LFS
  using (LFSet; trunc; _++_)
  renaming ([] to []S; _∷_ to _∷S_)
open import Cubical.HITs.ListedFiniteSet.Properties as LFSP
open import Cubical.Categories.Functor.Properties
  using (F-rUnit; F-lUnit; F-assoc)
open import Cubical.Categories.NaturalTransformation.Base
  using (makeNatTransPathP)
open import Cubical.Data.List using (List; []; _∷_)

open LFS

open LFSP

open Choices

open Zero

SET₀ = SET lzero

SET₀WithTerminal : CategoryWithTerminal (lsuc lzero) lzero
SET₀WithTerminal = SETWithTerminal lzero

LFSetFunctor : Functor SET₀ SET₀
LFSetFunctor .Functor.F-ob (A , isSetA) = LFSet A , trunc
LFSetFunctor .Functor.F-hom f = map f
LFSetFunctor .Functor.F-id {x = A} = funExt idₘap
  where
  idₘap : ∀ (xs : LFSet (A .fst)) → map (λ x → x) xs ≡ xs
  idₘap []S = refl
  idₘap (x ∷S xs) = cong (x ∷S_) (idₘap xs)
  idₘap (dup x xs i) j = dup x (idₘap xs j) i
  idₘap (comm x y xs i) j = comm x y (idₘap xs j) i
  idₘap (trunc xs ys p q i k) j =
    trunc (idₘap xs j) (idₘap ys j)
          (cong (λ z → idₘap z j) p) (cong (λ z → idₘap z j) q)
          i k

LFSetFunctor .Functor.F-seq f g = funExt seqMap
  where
  seqMap : ∀ xs → map (λ x → g (f x)) xs ≡ map g (map f xs)
  seqMap []S = refl
  seqMap (x ∷S xs) = cong (g (f x) ∷S_) (seqMap xs)
  seqMap (dup x xs i) j = dup (g (f x)) (seqMap xs j) i
  seqMap (comm x y xs i) j = comm (g (f x)) (g (f y)) (seqMap xs j) i
  seqMap (trunc xs ys p q i k) j =
    trunc (seqMap xs j) (seqMap ys j)
          (cong (λ z → seqMap z j) p) (cong (λ z → seqMap z j) q)
          i k

flattenLFSet : ∀ {A : Type lzero} → LFSet (LFSet A) → LFSet A
flattenLFSet []S = []S
flattenLFSet (xs ∷S xss) = xs ++ flattenLFSet xss
flattenLFSet (dup xs xss i) =
  ( xs ++ (xs ++ flattenLFSet xss)
      ≡⟨ assoc-++ xs xs (flattenLFSet xss) ⟩
    (xs ++ xs) ++ flattenLFSet xss
      ≡⟨ cong (_++ flattenLFSet xss) (idem-++ xs) ⟩
    xs ++ flattenLFSet xss ∎
  ) i
flattenLFSet (comm xs ys xss i) =
  ( xs ++ (ys ++ flattenLFSet xss)
      ≡⟨ assoc-++ xs ys (flattenLFSet xss) ⟩
    (xs ++ ys) ++ flattenLFSet xss
      ≡⟨ cong (_++ flattenLFSet xss) (comm-++ xs ys) ⟩
    (ys ++ xs) ++ flattenLFSet xss
      ≡⟨ sym (assoc-++ ys xs (flattenLFSet xss)) ⟩
    ys ++ (xs ++ flattenLFSet xss) ∎
  ) i
flattenLFSet (trunc xs ys p q i j) =
  trunc (flattenLFSet xs) (flattenLFSet ys)
        (cong flattenLFSet p) (cong flattenLFSet q) i j

map-++ :
  ∀ {A B : Type lzero} (f : A → B) (xs ys : LFSet A) →
    map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f xs ys =
  PropElim.f
    refl
    (λ x {s} ind → cong (f x ∷S_) ind)
    (λ s → trunc (map f (s ++ ys)) (map f s ++ map f ys))
    xs

flattenLFSet-nat :
  ∀ {A B : Type lzero} (f : A → B) (xss : LFSet (LFSet A)) →
    map f (flattenLFSet xss) ≡
      flattenLFSet (map (map f) xss)
flattenLFSet-nat f =
  PropElim.f
    refl
    (λ xs {xss} ind →
      map-++ f xs (flattenLFSet xss) ∙ cong (map f xs ++_) ind)
    (λ s → trunc (map f (flattenLFSet s))
                 (flattenLFSet (map (map f) s)))

ηLFSet : NatTrans Id LFSetFunctor
N-ob ηLFSet (A , _) x = x ∷S []S
N-hom ηLFSet f = refl

μLFSet : NatTrans (LFSetFunctor ∘F LFSetFunctor) LFSetFunctor
N-ob μLFSet (A , _) xss = flattenLFSet xss
N-hom μLFSet f = funExt (λ xss → sym (flattenLFSet-nat f xss))

idl-pointwise : ∀ {A : Type lzero} (xs : LFSet A) → flattenLFSet (xs ∷S []S) ≡ xs
idl-pointwise xs = comm-++-[] xs

idr-pointwise :
  ∀ {A : Type lzero} (xs : LFSet A) →
    flattenLFSet (map (λ x → x ∷S []S) xs) ≡ xs
idr-pointwise =
  PropElim.f
    refl
    (λ x {xs} ind → cong (x ∷S_) ind)
    (λ s → trunc (flattenLFSet (map (λ x → x ∷S []S) s)) s)

flatten-++ :
  ∀ {A : Type lzero} (xss yss : LFSet (LFSet A)) →
    flattenLFSet (xss ++ yss) ≡ flattenLFSet xss ++ flattenLFSet yss
flatten-++ xss yss =
  PropElim.f
    refl
    (λ xs {xss} ind →
      xs ++ flattenLFSet (xss ++ yss) ≡⟨ cong (xs ++_) ind ⟩
      xs ++ (flattenLFSet xss ++ flattenLFSet yss)
        ≡⟨ assoc-++ xs (flattenLFSet xss) (flattenLFSet yss) ⟩
      (xs ++ flattenLFSet xss) ++ flattenLFSet yss ∎)
    (λ s → trunc (flattenLFSet (s ++ yss))
                 (flattenLFSet s ++ flattenLFSet yss))
    xss

assoc-pointwise :
  ∀ {A : Type lzero} (xsss : LFSet (LFSet (LFSet A))) →
    flattenLFSet (flattenLFSet xsss) ≡
      flattenLFSet (map flattenLFSet xsss)
assoc-pointwise =
  PropElim.f
    refl
    (λ xss {xsss} ind →
      flattenLFSet (xss ++ flattenLFSet xsss)
        ≡⟨ flatten-++ xss (flattenLFSet xsss) ⟩
      flattenLFSet xss ++ flattenLFSet (flattenLFSet xsss)
        ≡⟨ cong (flattenLFSet xss ++_) ind ⟩
      flattenLFSet xss ++ flattenLFSet (map flattenLFSet xsss) ∎)
    (λ s → trunc (flattenLFSet (flattenLFSet s))
                 (flattenLFSet (map flattenLFSet s)))

instance
  LFSetIsMonad : IsMonad LFSetFunctor
  η LFSetIsMonad = ηLFSet
  μ LFSetIsMonad = μLFSet
  idl-μ LFSetIsMonad =
    makeNatTransPathP F-rUnit refl (λ i (A , _) → funExt idl-pointwise i)
  idr-μ LFSetIsMonad =
    makeNatTransPathP F-lUnit refl (λ i (A , _) → funExt idr-pointwise i)
  assoc-μ LFSetIsMonad =
    makeNatTransPathP F-assoc refl
      (λ i (A , _) → funExt (λ xsss → sym (assoc-pointwise xsss)) i)

-- A family of sets is non-empty if every constituent set has an element.
IsNonEmptyFamily : ∀ {A : Type lzero} → LFSet (LFSet A) → Type lzero
IsNonEmptyFamily {A} xss =
  ∀ (S : LFSet A) → (S ∈ xss) .fst → Σ[ x ∈ A ] ((x ∈ S) .fst)

postulate
  -- allChoices transforms a set of sets into the set of all choice sets:
  -- each choice set selects one element from each constituent set.
  allChoices : ∀ {A : Type lzero} → LFSet (LFSet A) → LFSet (LFSet A)

  allChoices-nat :
    ∀ {A B : Type lzero} (f : A → B) (xss : LFSet (LFSet A)) →
      map (map f) (allChoices xss) ≡
        allChoices (map (map f) xss)

  -- For a non-empty family, the union of all choices absorbs to the union of sets:
  allChoices-union-absorption :
    ∀ {A : Type lzero} (xss : LFSet (LFSet A))
    → IsNonEmptyFamily xss
    → flattenLFSet (allChoices xss) ≡ flattenLFSet xss

-- TODO : rename to χLFSet
choicesLFSet :
  NatTrans (LFSetFunctor ∘F LFSetFunctor) (LFSetFunctor ∘F LFSetFunctor)
N-ob choicesLFSet (A , _) = allChoices
N-hom choicesLFSet f = funExt (λ xss → sym (allChoices-nat f xss))

postulate
  lfset-choices-union-absorption :
    ∀ {Z : Category.ob SET₀} →
      (transformationMorphism (μ LFSetIsMonad) Z ∘ transformationMorphism choicesLFSet Z)
        ≡ transformationMorphism (μ LFSetIsMonad) Z

instance
  LFSetChoices : Choices SET₀ LFSetFunctor LFSetIsMonad
  χ LFSetChoices = choicesLFSet
  choices-union-absorption LFSetChoices {Z = Z} =
    lfset-choices-union-absorption {Z = Z}

-- TODO : rename to ζLFSet
zeroLFSet : NatTrans LFSetFunctor LFSetFunctor
N-ob zeroLFSet (A , _) _ = []S
N-hom zeroLFSet f = refl

postulate
  lfset-zero-absorption :
    ∀ {Z : Category.ob SET₀}
      (f : SET₀ [ LFSetFunctor ⟅ Z ⟆ , LFSetFunctor ⟅ Z ⟆ ]) →
      f ∘ transformationMorphism zeroLFSet Z ≡
        transformationMorphism zeroLFSet Z

instance
  LFSetZero : Zero SET₀ LFSetFunctor
  ζ LFSetZero = zeroLFSet
  zero-absorption LFSetZero {Z = Z} f =
    lfset-zero-absorption {Z = Z} f

globalLFSetProsetStr :
  (Y : Category.ob SET₀) →
    ProsetStr lzero (GlobalElement SET₀WithTerminal (LFSetFunctor ⟅ Y ⟆))
globalLFSetProsetStr Y = prosetstr _≲ₘ_ isProsetₘ
  where
  _≲ₘ_ :
    GlobalElement SET₀WithTerminal (LFSetFunctor ⟅ Y ⟆) →
    GlobalElement SET₀WithTerminal (LFSetFunctor ⟅ Y ⟆) →
    Type lzero
  f ≲ₘ g = ∀ (x : Y .fst) →
             (x ∈ f tt*) .fst → (x ∈ g tt*) .fst

  isProsetₘ : IsProset _≲ₘ_
  IsProset.is-set isProsetₘ =
    SET₀ .Category.isSetHom
      {x = CategoryWithTerminal.1C SET₀WithTerminal}
      {y = LFSetFunctor ⟅ Y ⟆}
  IsProset.is-prop-valued isProsetₘ f g =
    isPropΠ (λ x → isProp→ ((x ∈ g tt*) .snd))
  IsProset.is-refl isProsetₘ f x p = p
  IsProset.is-trans isProsetₘ f g h fg gh x p = gh x (fg x p)
```
## Recursive Compositional Structure: `PreThingTree`

We define an inductive compositional structure `PreThingTree` that builds arbitrary
composite hierarchies from atomic potentials. A pre-thing is either:
1. `atomic`: an underlying potential from `Pₘ`, or
2. `composite`: a finite collection (`LFSet`) of sub-pre-things.

Higher-inductive truncation `truncPreThingTree` guarantees that `PreThingTree Z` is a 0-type
(a set in homotopy type theory):

```agda
data PreThingTree (Z : Type lzero) : Type lzero where
  atomic            : Z → PreThingTree Z
  composite         : LFSet (PreThingTree Z) → PreThingTree Z
  truncPreThingTree : isSet (PreThingTree Z)

PreThingTree-isSet : ∀ {Z : Type lzero} → isSet (PreThingTree Z)
PreThingTree-isSet = truncPreThingTree
```

## Concrete Realization: Partial Implementation of `Reality` and `PreOrderedReality`

With the material universe formalized as `SET₀` and the collection structure materialized
as finite sets (`LFSetFunctor`), we can now provide partial implementations of `Reality`
and `PreOrderedReality`.

Arbitrary compositional pre-thing hierarchies are realized via `PreThingTree (Pₘ .fst)`,
enabling immediate implementations of `potentialAsPreThingMorphism` (as `atomic`) and
`preThingCollectionAsPreThingMorphism` (as `composite`). Furthermore, the predicate
`isGlobalPreThingSingleton` is concretely realized by requiring each image element
to be a singleton `{ x }`. All material collection requirements
(`CFₘ`, `materialCollectionIsMonad`, `materialCollectionZero`,
`materialCollectionChoices`, and `globalPreThingCollectionProsetStr`) are resolved
automatically inside `MaterialReality`:

```agda
record MaterialReality
    (Cᵥ : Category (lsuc lzero) lzero)
    (CFᵥ : Functor Cᵥ Cᵥ)
    (PFₘᵥ : Profunctor⊶ (lsuc lzero) lzero SET₀ Cᵥ)
    (Uᵥ : Category.ob Cᵥ)
    (Pₘ : Category.ob SET₀) :
      Type (lsuc (lsuc lzero)) where

  PreThing : Category.ob SET₀
  PreThing = PreThingTree (Pₘ .fst) , truncPreThingTree

  potentialAsPreThingMorphism : SET₀ [ Pₘ , PreThing ]
  potentialAsPreThingMorphism = atomic

  preThingCollectionAsPreThingMorphism :
    SET₀ [ LFSetFunctor ⟅ PreThing ⟆ , PreThing ]
  preThingCollectionAsPreThingMorphism = composite

  isGlobalPreThingSingleton :
    GlobalElement SET₀WithTerminal (LFSetFunctor ⟅ PreThing ⟆) → Type lzero
  isGlobalPreThingSingleton f =
    Σ[ x ∈ PreThing .fst ] (f tt* ≡ x ∷S []S)

  field
    prePlaceFunctor :
      Functor Cᵥ Cᵥ

    preThingCollectionFunctor :
      Functor Cᵥ SET₀

  open Profunctor⊶ PFₘᵥ

  field
    preThingCollectionPathEquality :
      preThingCollectionFunctor ⟅ Uᵥ ⟆ ≡ LFSetFunctor ⟅ PreThing ⟆

    isGlobalPreInteraction :
      GlobalElement SET₀WithTerminal (LFSetFunctor ⟅ PreThing ⟆) → Type lzero

    preThingCollectionAsPreInteractionMorphism :
      SET₀ [ LFSetFunctor ⟅ PreThing ⟆ , LFSetFunctor ⟅ PreThing ⟆ ]

    preThingCollectionPrePlaceHeteroMorphism :
      Het[ LFSetFunctor ⟅ PreThing ⟆ , prePlaceFunctor ⟅ Uᵥ ⟆ ]

    preThingSingletonPrePlaceHeteroMorphismLift :
      Het[ LFSetFunctor ⟅ PreThing ⟆ , prePlaceFunctor ⟅ Uᵥ ⟆ ] →
        Het[ LFSetFunctor ⟅ LFSetFunctor ⟅ PreThing ⟆ ⟆ ,
             CFᵥ ⟅ prePlaceFunctor ⟅ Uᵥ ⟆ ⟆ ]

    instance
      universeTransitionProsetStr :
        ProsetStr lzero (Cᵥ [ Uᵥ , Uᵥ ])

      globalHeteroPrePlaceProsetStr :
        ProsetStr lzero
          Het[ CategoryWithTerminal.1C SET₀WithTerminal , prePlaceFunctor ⟅ Uᵥ ⟆ ]

      prePlaceMorphismSupremum :
        Supremum Cᵥ CFᵥ
          (prePlaceFunctor ⟅ Uᵥ ⟆)

  reality : Reality Cᵥ SET₀WithTerminal CFᵥ LFSetFunctor PFₘᵥ Uᵥ Pₘ

  Reality.prePlaceFunctor reality = prePlaceFunctor
  Reality.PreThing reality = PreThing
  Reality.potentialAsPreThingMorphism reality = potentialAsPreThingMorphism
  Reality.preThingCollectionFunctor reality = preThingCollectionFunctor
  Reality.materialCollectionIsMonad reality = LFSetIsMonad
  Reality.materialCollectionZero reality = LFSetZero
  Reality.materialCollectionChoices reality = LFSetChoices
  Reality.preThingCollectionPathEquality reality = preThingCollectionPathEquality
  Reality.isGlobalPreThingSingleton reality = isGlobalPreThingSingleton
  Reality.isGlobalPreInteraction reality = isGlobalPreInteraction
  Reality.preThingCollectionAsPreThingMorphism reality =
    preThingCollectionAsPreThingMorphism
  Reality.preThingCollectionAsPreInteractionMorphism reality =
    preThingCollectionAsPreInteractionMorphism
  Reality.preThingCollectionPrePlaceHeteroMorphism reality =
    preThingCollectionPrePlaceHeteroMorphism
  Reality.preThingSingletonPrePlaceHeteroMorphismLift reality =
    preThingSingletonPrePlaceHeteroMorphismLift
  Reality.universeTransitionProsetStr reality = universeTransitionProsetStr
  Reality.globalPreThingCollectionProsetStr reality =
    globalLFSetProsetStr PreThing
  Reality.globalHeteroPrePlaceProsetStr reality =
    globalHeteroPrePlaceProsetStr
  Reality.prePlaceMorphismSupremum reality = prePlaceMorphismSupremum

record MaterialPreOrderedReality
    (CWTᵥ : CategoryWithTerminal (lsuc lzero) lzero)
    (CFᵥ : Functor (CategoryWithTerminal.category CWTᵥ)
                   (CategoryWithTerminal.category CWTᵥ))
    (PFₘᵥ : Profunctor⊶ (lsuc lzero) lzero SET₀ (CategoryWithTerminal.category CWTᵥ))
    (Uᵥ : Category.ob (CategoryWithTerminal.category CWTᵥ))
    (Pₘ : Category.ob SET₀) :
      Type (lsuc (lsuc lzero)) where
  field
    materialReality :
      MaterialReality (CategoryWithTerminal.category CWTᵥ) CFᵥ PFₘᵥ Uᵥ Pₘ

    instance
      virtualUniverseGlobalElementProsetStr :
        ProsetStr lzero (GlobalElement CWTᵥ Uᵥ)

    virtualUniverseElement :
      GlobalElement CWTᵥ Uᵥ

  open MaterialReality materialReality public

  preOrderedReality :
    PreOrderedReality CWTᵥ CFᵥ LFSetFunctor PFₘᵥ Uᵥ Pₘ

  PreOrderedReality.reality preOrderedReality = reality

  PreOrderedReality.virtualUniverseGlobalElementProsetStr preOrderedReality =
    virtualUniverseGlobalElementProsetStr

  PreOrderedReality.virtualUniverseElement preOrderedReality =
    virtualUniverseElement
```
