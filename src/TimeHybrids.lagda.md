# Formalizing Fred Van Oystaeyen's "Time Hybrids"

This document presents a *formalization* of a *mathematical abstraction* of the *basics* of
Fred Van Oystaeyen's book, *Time Hybrids: A New Generic Theory of Reality*.

Fred, an outstanding mathematician, is a pioneer on *noncommutative algebraic geometry*. Among
others he wrote the book *Virtual topology and Functor geometry* that contributes to the
underlying mathematical abstraction of his *Time Hybrids: A New Generic Theory of Reality*
book.

Frankly, my mathematical abstraction is not fully in sync with Fred's mathematical abstraction
in his *Virtual topology and Functor geometry* book.

My goal was to formalize the underlying mathematical abstraction of the basics of Fred's book
*computationally* in a *pointfree* way.

## Choices

There are two fundamental choices to be made.

### Mathematical Abstractions

*Please read diagonally if you are not inclined.* 

I *model* Fred's *Theory of Reality* using the following mathematical abstractions.

- **Categories**: Both the *virtual universe* and the *material universe* are modeled as
  categories. A category comes with *objects* and *homomorphisms* between objects.

- **Transitions**: *Dynamic evolution* is modeled as *endomorphisms*, which are homomorphisms 
  from objects to theirselves. We refer to them as *transitions*.

- **Functors**: The dynamic evolution of *universe objects* — such as *virtual pre-places*
  and *material pre-thing collections* — is modeled using *functors* that map 
  *virtual universe transitions* to *(virtual or material) universe object transitions*.

- **Profunctors**: The inter-action between the virtual universe and the material universe is
  modeled as a *profunctor* between them. A profunctor comes with *heteromorphisms* between
  universe objects — such as material pre-thing collections and virtual pre-places — . More
  precisely, the cross-category connection between material pre-thing collections and virtual
  pre-places, the pre-place of a pre-thing collection, is modeled as a heteromorphism, upon
  which material *pre-thing collection transitions* *act contravariantly* at left and virtual 
  *pre-place transitions* *act covariantly* at right, respectively.

Note that I used the word *inter-action* to emphasize that both pre-thing collection
transitions and pre-place transitions act upon the pre-place of a pre-thing collection.

### Formal Framework

*Please read diagonally if you are not inclined.* 

I *formalize* this modeling in **`Cubical Agda`**, based upon *Cubical Homotopy Type Theory*,
rather than standard `Agda` or `Lean 4`, motivated by several computational principles.

- **Computational Path Equality**: In `Cubical Agda`, type equality is not structural
  inductive equality but *path equality* at abstract interval *dimensions* `I`, `J`, ... .
  Under the hood, structural induction computes directly using `transp` / `transport` at path
  intervals.

- **Computational Univalence**: The *Univalence Principle* states that type equivalence
  (`_≃_`) is equivalent to type equality (`_≡_`). In `Cubical Agda`, univalence computes
  natively via `ua` and `pathToEquiv` (which we rename to `equivToEqual` and `equalToEquiv`),
  allowing structural equivalences to be, well, equivalent to path equalities without needing
  unproven `postulate`s. Type equality lives at a higher *type universe level* than type
  equivalence. Equivalence, `T₁ ≃ T₂`, looks *inside* the types at their elements.
  Equality `T₁ ≡ T₂` looks *from above*, treating the types as elements of a higher type
  universe level.

Frankly, my choice for `Cubical Agda` is also motivated by *personal* preferences.
`Cubical Agda` is an academic effort, while `Lean 4` is an established effort sponsored by
important companies (you name them) and, as such, is also an industrial effort. I know that
important results are achieved using `Lean 4`. I also know that Terence Tao recognizes
that `Cubical Agda`, based upon Homotopy Type Theory (HoTT), has advantages compared to
`Lean 4`. 

Below is a quote of Terence Tao.

*My own work does not interact with HoTT, but there are other areas of mathematics for which 
HOTT is a promising foundation. It isn't very well supported in `Lean 4` at the moment. My 
understanding is that Cubical Agda is currently the formal language that has the most support
for HOTT.* 

As far as I am concerned, the following is striking.

- **Harmonizing Paths and Transitions**: Category theory provides transitions **at** which
  state evolves. Homotopy Type Theory (HoTT) provides paths **at** which equality is
  structurally `transp`orted. In my formalization, these two concepts work in complete harmony.
  For example, equalities between types are transported to equalities between transition types.
  Note that I wrote *transitions at*, emphasising that, just as Fred, I consider *continous*
  transitions to be *discrete* entities. Similarly, note that I wrote *paths at*, emphasising
  that I consider *continuos* paths to be discrete entities. After all, under the hood, they
  correspond to structural induction which is discrete.

### Naming conventions

As far as naming conventions are concerned we use abbreviations for names of Time Hybrids
independent concepts and full names for Time Hybrids dependent concepts.

For example, see below, we use abbreviated `Trans` and `Coll` for transitions and collections
respectively, and, see below, we use `PreThing` and `Potential` for pre-things and potentials
respectively.

I find adhering to naming conventions in a consistent way notoriously hard. Especially when
comining domain specific dependent concepts with domain specific independent concepts.

I'll try to do my best, but, please, suggest improvements.

### Why Profunctors matter.

Profunctors,
see [nLab](https://ncatlab.org/nlab/show/profunctor)
and their `Cubical Agda` specification
see [Agda](https://github.com/agda/cubical/blob/master/Cubical/Categories/Profunctor/Base.agda)
turned out to be the natural abstraction to *formally separate* virtual universe related
entities from material universe related entities.

It is perfectly possible to go for other abstractions, but, as far as I know, they rely on
pre-places to belong to both the virtual universe and the material universe. As such they are,
in my humble opinion, sub-optimal abstractions.

Note that the *formalization* of the abstractions imposed pre-places to belong to both the
virtual universe and the material universe. I consider this as a formal "double-check" of
*type systems*, as the one of `Cubical Agda`, to inform you about the consequences of the
abstraction choice you have made.

**All comments are welcome.**

## How the `Reality` abstraction is formalized incrementally

I am a mathematician. As such I am interested in the least complex general abstractions that
enabled me to formalize concepts of Fred's book as `Cubical Agda` specifications. Of course,
eventually, those abstractions and `Cubical Agda` specifications will become more complex.
Moreover, eventually, those abstractions and `Cubical Agda` specifications will become more
specific as (partial) concretions and (partial) `Cubical Agda` implementations respectively.

## Introducing definitions and modules "by need"

We structure the specification by introducing standard libraries, definitions, and types
**by need**—importing and declaring entities precisely at the point in the development where
they are required.

To begin with `Reality01`, we need primitive levels, cubical paths, categories, functors,
constant functors, and profunctors:

```agda
{-# OPTIONS --cubical --guardedness #-}

module TimeHybrids where

open import Agda.Primitive

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Profunctor.Base
```

## The `Reality01` specification

The specification `record Reality01` brings together the *virtual universe*, the
*material universe*, and how they *inter-act upon each other*.

### Parameters

`record Reality01` is parameterized by:

- `Catᵥ`: the *virtual universe category*.

- `Uᵥ`: a designated virtual universe object (the *state* or *time* of the virtual universe).

- `Catₘ`: the *material universe category*.

- `CollFunctₘ`: the *material collection functor*, formalizing material to-collection mappings.

- `Profunctₘᵥ`: the *material-virtual profunctor*, formalizing the inter-action.

First also define a synonym `Propertyₕ` for `Type h`.

```agda
record Reality01 {o h : Level}
    (Catᵥ : Category o h)
    (Uᵥ : Category.ob Catᵥ)
    (Catₘ : Category o h)
    (CollFunctₘ : Functor Catₘ Catₘ)
    (Profunctₘᵥ : Profunctor⊶ o h Catₘ Catᵥ) :
  Type (lsuc (o ⊔ h)) where

  Propertyₕ = Type h
```

### Convenient renamings and transition synonyms

We introduce notation for homomorphism-types and transition-types.

```agda
  open Category Catᵥ renaming (ob to obᵥ; _∘_ to _∘ᵥ_)
  open Category Catₘ renaming (ob to obₘ; _∘_ to _∘ₘ_)

  Homᵥ[_,_] : obᵥ → obᵥ → Type h
  Homᵥ[_,_] = Catᵥ [_,_]

  Homₘ[_,_] : obₘ → obₘ → Type h
  Homₘ[_,_] = Catₘ [_,_]

  Transᵥ[_] : obᵥ → Type h
  Transᵥ[ Z ] = Homᵥ[ Z , Z ]

  Transₘ[_] : obₘ → Type h
  Transₘ[ Z ] = Homₘ[ Z , Z ]
```

We also define left-to-right composition operators.

```agda
  _⋙ᵥ_ : ∀ {Z Y X : obᵥ} → Homᵥ[ Z , Y ] → Homᵥ[ Y , X ] → Homᵥ[ Z , X ]
  f ⋙ᵥ g = g ∘ᵥ f

  infixl 8 _⋙ᵥ_

  _⋙ₘ_ : ∀ {Z Y X : obₘ} → Homₘ[ Z , Y ] → Homₘ[ Y , X ] → Homₘ[ Z , X ]
  f ⋙ₘ g = g ∘ₘ f

  infixl 8 _⋙ₘ_
```

### Profunctor heteromorphisms and actions

We introduce notation for heteromomorphism-types.

```agda
  open Profunctor⊶ Profunctₘᵥ

  Hetₘᵥ[_,_] : obₘ → obᵥ → Type h
  Hetₘᵥ[_,_] = Het[_,_]
```
Heteromorphisms between material objects and virtual objects are equipped with left 
contravariant actions upon them by material transitions and right covariant actions upon them
by virtual transitions.

```agda
  _ₗ∘_ : ∀ {Zₘ Yₘ : obₘ} {Xᵥ : obᵥ} → Homₘ[ Zₘ , Yₘ ] → Hetₘᵥ[ Yₘ , Xᵥ ] → Hetₘᵥ[ Zₘ , Xᵥ ]
  _ₗ∘_ = _⋆L_

  infixl 9 _ₗ∘_

  _∙ᵣ_ : ∀ {Zₘ : obₘ} {Yᵥ Xᵥ : obᵥ} → Hetₘᵥ[ Zₘ , Yᵥ ] → Homᵥ[ Yᵥ , Xᵥ ] → Hetₘᵥ[ Zₘ , Xᵥ ]
  _∙ᵣ_ = _⋆R_

  infixr 8 _∙ᵣ_
```

### Designated objects, pre-places and pre-thing collections, with their dynamic evolutions

- `PrePlaceᵥ` is declared as an object `obᵥ`.

- `prePlaceFunctor` is declared as a functor `Functor Catᵥ Catᵥ` mapping a virtual transition
  to a pre-place transitions making pre-places dynamic.

- `PreThingₘ` is declared as an `an object `obₘ`.

- `Potentialₘ` is declared as an an object `obₘ`. representing atomic pre-things as declared by
  `potentialAsAtomicPreThing`.

- `PreThingCollₘ` is defined as `CollFunctₘ ⟅ PreThingₘ ⟆` representing composite pre-things as
  declared by `preThingCollAsCompositePreThing`.

- `preThingCollFunct` is declared as a functor `Functor Catᵥ Catₘ` mapping a virtual transition
  to a pre-thing collection transition making pre-thing collections dynamic.

- `preThingCollPrePlace` is declared as a heteromorphism 
  `Hetₘᵥ[ PreThingCollₘ , PrePlaceᵥ ]` connecting a material pre-thing collection to a
  virtual pre-place.

`potentialAsAtomicPreThingFunctor` and `preThingCollAsCompositePreThing` declare pre-things to
be compositional in a recursive way . Pre-things are either potentials, being atomic
pre-things, or pre-thing collections, being composite pre-things. Frankly, for now we do not
yet make use of this recursive compositionality, but we introduce it already anyway.

```agda
  field
    PrePlaceᵥ : obᵥ

    prePlaceFunctor : Functor Catᵥ Catᵥ
    prePlaceFunctor⟅Uᵥ⟆≡PrePlaceᵥ : prePlaceFunctor ⟅ Uᵥ ⟆ ≡ PrePlaceᵥ

    PreThingₘ : obₘ

    Potentialₘ : obₘ

    potentialAsAtomicPreThing : Homₘ[ Potentialₘ ,  PreThingₘ ]

  PreThingCollₘ : obₘ
  PreThingCollₘ = CollFunctₘ ⟅ PreThingₘ ⟆

  field
    preThingCollAsCompositePreThing : Homₘ[ PreThingCollₘ ,  PreThingₘ ]

    preThingCollFunct : Functor Catᵥ Catₘ
    preThingCollFunct⟅Uᵥ⟆≡PreThingCollₘ : preThingCollFunct ⟅ Uᵥ ⟆ ≡ PreThingCollₘ

    preThingCollPrePlace : Hetₘᵥ[ PreThingCollₘ , PrePlaceᵥ ]
```

### Packaged pre-place functor

Pre-place evolution is packaged into `PrePlaceFunctor`.

```agda
  record PrePlaceFunctor : Type (o ⊔ h) where
    constructor ppf
    pattern
    field
      functor : Functor Catᵥ Catᵥ
      functor⟅Uᵥ⟆≡PrePlaceᵥ : functor ⟅ Uᵥ ⟆ ≡ PrePlaceᵥ

  open PrePlaceFunctor
```

### Movement

The property-valued operation `_isMovementAt_` defines a pre-place evolution to be a pre-thing
collection movement under a universe transition.

```agda
  _isMovementAt_ : PrePlaceFunctor → Transᵥ[ Uᵥ ] → Propertyₕ
  _isMovementAt_ (ppf functor functor⟅Uᵥ⟆≡PrePlaceᵥ) transᵥ[Uᵥ] =
    let 
      transᵥ[PrePlaceᵥ] : Transᵥ[ PrePlaceᵥ ]
      transᵥ[PrePlaceᵥ] =
        transport
          (λ i → Transᵥ[ prePlaceFunctor⟅Uᵥ⟆≡PrePlaceᵥ i ])
          (prePlaceFunctor ⟪ transᵥ[Uᵥ] ⟫)

      transₘ[PreThingCollₘ] : Transₘ[ PreThingCollₘ ]
      transₘ[PreThingCollₘ] =
        transport
          (λ i → Transₘ[ preThingCollFunct⟅Uᵥ⟆≡PreThingCollₘ i ])
          (preThingCollFunct ⟪ transᵥ[Uᵥ] ⟫)

      movement : Transᵥ[ PrePlaceᵥ ]
      movement =
        transport
          (λ i → Transᵥ[ functor⟅Uᵥ⟆≡PrePlaceᵥ i ])
          (functor ⟪ transᵥ[Uᵥ] ⟫)
    in 
        (transₘ[PreThingCollₘ] ₗ∘ preThingCollPrePlace) ∙ᵣ movement
      ≡ preThingCollPrePlace ∙ᵣ transᵥ[PrePlaceᵥ]
```

Notice how HoTT naturally `transport`s object equality, `≡`, along an interval to define a
transition at the end of the interval in terms of the transition at the start of the interval

### Immobility as constant pre-place functor

Immobility is defined by no movement, formalized as a constant pre-place functor.

```agda
  noMovementFunctor : PrePlaceFunctor
  noMovementFunctor = ppf (Constant Catᵥ Catᵥ PrePlaceᵥ) refl

  isImmobileAt : Transᵥ[ Uᵥ ] → Propertyₕ
  isImmobileAt transᵥ[Uᵥ] = noMovementFunctor isMovementAt transᵥ[Uᵥ]
```

## The `Reality02` specification

The specification `record Reality02` builds upon `record Reality01` adding
the following mathematical abstraction.

- **Terminals**: The material universe is now modeled as a category with *terminal* objects in
  order to state material universe entity properties in a pointfree way.

The specification `record Reality02` formalizes the preservation of a pre-thing collection
being a pre-interaction regarding universe transitions.

We import terminal limits to model global elements.

`reality01` is a declaration that can be used to access the declarations and definitions of
`Reality01` (in `Reality02` and later versions) by opening it `public` using
`open Reality01 reality01 public`. 

`terminalₘ` is a declaration that can be used to access the declarations and definitions of
`Terminal`.

We inherit by delegation.

```agda
open import Cubical.Categories.Limits.Terminal

record Reality02 {o h : Level}
    (Catᵥ : Category o h)
    (Uᵥ : Category.ob Catᵥ)
    (Catₘ : Category o h)
    (CollFunctₘ : Functor Catₘ Catₘ)
    (Profunctₘᵥ : Profunctor⊶ o h Catₘ Catᵥ) :
  Type (lsuc (o ⊔ h)) where

  open Category Catₘ renaming (ob to obₘ)

  field
    reality01 : Reality01 Catᵥ Uᵥ Catₘ CollFunctₘ Profunctₘᵥ

  open Reality01 reality01 public
  
  field
    terminalₘ : Terminal Catₘ

  1ₘ : obₘ
  1ₘ = terminalOb Catₘ terminalₘ
  
  PreInteractionₘ : obₘ
  PreInteractionₘ = PreThingCollₘ 

  field 
    isPreInteraction : Homₘ[ 1ₘ , PreThingCollₘ ] → Propertyₕ 

  PreInteractionPreservation : Propertyₕ
  PreInteractionPreservation =
    ∀ (transᵥ[Uᵥ] : Transᵥ[ Uᵥ ]) 
      (homₘ[1ₘ,PreThingCollₘ] : Homₘ[ 1ₘ , PreThingCollₘ ])
    → isPreInteraction 
        homₘ[1ₘ,PreThingCollₘ] 
      → isPreInteraction 
          (homₘ[1ₘ,PreThingCollₘ] ⋙ₘ
            transport
              (λ i → Transₘ[ preThingCollFunct⟅Uᵥ⟆≡PreThingCollₘ i ])
              (preThingCollFunct ⟪ transᵥ[Uᵥ] ⟫))
```

Notice that the property-valued function name `isPreInteraction`, although it names a 
property valued function dealing with global elements, simply refers to the elements involved.

We (try to) adhere to this naming simplification in a consistent way.

## The `Reality03` specification

The specification `record Reality03` adds the following mathematical abstraction.

- **Empty**: A material universe category *natural transformation* from a functor to itself.

The specification `record Reality03` formalizes the no escape from a to empty pre-thing 
collection transition. 

We import natural transformations.

`N-ob` formalizes the object part of natural transformations, in this case natural
transformation `ε`.

```agda
open import Cubical.Categories.NaturalTransformation.Base

open NatTrans

record Empty
    {o h : Level}
    (C : Category o h)
    (F : Functor C C) :
  Type (lsuc (ℓ-max o h)) where

  open Category C

  field
    ε : NatTrans F F

  field
    emptyAbsorption :
      ∀ {Z : Category.ob C}
        (f : C [ F ⟅ Z ⟆ , F ⟅ Z ⟆ ])
      → f ∘ N-ob ε Z ≡ N-ob ε Z

open Empty {{...}} public

record Reality03 {o h : Level}
    (Catᵥ : Category o h)
    (Uᵥ : Category.ob Catᵥ)
    (Catₘ : Category o h)
    (CollFunctₘ : Functor Catₘ Catₘ)
    (Profunctₘᵥ : Profunctor⊶ o h Catₘ Catᵥ) :
  Type (lsuc (o ⊔ h)) where

  field
    reality02 : Reality02 Catᵥ Uᵥ Catₘ CollFunctₘ Profunctₘᵥ

  open Reality02 reality02 public
 
  field
    instance
      emptyₘ : Empty Catₘ CollFunctₘ

  NoEscapeFromToEmptyPreThingCollTrans : Propertyₕ
  NoEscapeFromToEmptyPreThingCollTrans =
    ∀ transᵥ[Uᵥ] 
    →   N-ob ε PreThingₘ ⋙ₘ 
        transport
          (λ i → Transₘ[ preThingCollFunct⟅Uᵥ⟆≡PreThingCollₘ i ])
          (preThingCollFunct ⟪ transᵥ[Uᵥ] ⟫)
      ≡ N-ob ε PreThingₘ

  noEscapeFromToEmptyPreThingCollTransEvidence : NoEscapeFromToEmptyPreThingCollTrans
  noEscapeFromToEmptyPreThingCollTransEvidence =
    λ transᵥ[Uᵥ]
    → emptyAbsorption (
        transport
          (λ i → Transₘ[ preThingCollFunct⟅Uᵥ⟆≡PreThingCollₘ i ])
          (preThingCollFunct ⟪ transᵥ[Uᵥ] ⟫)
      )
```

Notice that the specific evidence `noEscapeFromToEmptyPreThingCollTransEvidence` is an instance
of the general law `emptyAbsorption`.

## The `Reality04` specification

The specification `record Reality04` formalizes a pre-thing singletons equality involving `η`,
the unit of a monad structure on `CollFunctₘ`. 

We import monads and type equivalences.

```agda
open import Cubical.Categories.Monad.Base

open import Agda.Builtin.Cubical.Equiv

open IsMonad

record Reality04 {o h : Level}
    (Catᵥ : Category o h)
    (Uᵥ : Category.ob Catᵥ)
    (Catₘ : Category o h)
    (CollFunctₘ : Functor Catₘ Catₘ)
    (Profunctₘᵥ : Profunctor⊶ o h Catₘ Catᵥ) :
  Type (lsuc (o ⊔ h)) where

  open Category Catₘ

  field
    reality03 : Reality03 Catᵥ Uᵥ Catₘ CollFunctₘ Profunctₘᵥ

    instance
      isMonadₘ : IsMonad CollFunctₘ

  open Reality03 reality03 public

  field
    isPreThingSingleton : Homₘ[ 1ₘ , PreThingCollₘ ] → Propertyₕ

  preThingSingletonEquation : Homₘ[ 1ₘ , PreThingCollₘ ] → Propertyₕ
  preThingSingletonEquation homₘ[1ₘ,PreThingCollₘ] =
      homₘ[1ₘ,PreThingCollₘ]
    ≡     homₘ[1ₘ,PreThingCollₘ]
      ⋙ₘ preThingCollAsCompositePreThing
      ⋙ₘ N-ob (η isMonadₘ) PreThingₘ

  PreThingSingletonEquivalence : Propertyₕ
  PreThingSingletonEquivalence =
    ∀ (homₘ[1ₘ,PreThingCollₘ] : Homₘ[ 1ₘ , PreThingCollₘ ])
    →   isPreThingSingleton homₘ[1ₘ,PreThingCollₘ]
      ≃ preThingSingletonEquation homₘ[1ₘ,PreThingCollₘ]
```

## The `UnivalenceIllustration` specification

Equality is equivalence at a higher property level.

We import function composition and univalence (`ua` and `pathToEquiv`, renamed to 
`equivToEqual` and `equalToEquiv`).

```agda
open import Cubical.Foundations.Function renaming (_∘_ to _∘ᶠ_)
open import Cubical.Foundations.Univalence 
  renaming (ua to equivToEqual; pathToEquiv to equalToEquiv)

record UnivalenceIllustration {o h : Level}
    (Catᵥ : Category o h)
    (Uᵥ : Category.ob Catᵥ)
    (Catₘ : Category o h)
    (CollFunctₘ : Functor Catₘ Catₘ)
    (Profunctₘᵥ : Profunctor⊶ o h Catₘ Catᵥ) :
  Type (lsuc (o ⊔ h)) where

  Propertyₕ₊₁ = Type (lsuc h)

  field
    reality04 : Reality04 Catᵥ Uᵥ Catₘ CollFunctₘ Profunctₘᵥ

  open Reality04 reality04

  PreThingSingletonEquality : Propertyₕ₊₁
  PreThingSingletonEquality =
    ∀ (homₘ[1ₘ,PreThingCollₘ] : Homₘ[ 1ₘ , PreThingCollₘ ])
    →   isPreThingSingleton homₘ[1ₘ,PreThingCollₘ]
      ≡ preThingSingletonEquation homₘ[1ₘ,PreThingCollₘ]
```

Equality evidences and equivalence evidences can be defined in terms of each other.

```agda
  field
    preThingSingletonEquivalenceEvidence : PreThingSingletonEquivalence

  PreThingSingletonEqualityEvidence' : PreThingSingletonEquality
  PreThingSingletonEqualityEvidence' =
    equivToEqual ∘ᶠ preThingSingletonEquivalenceEvidence

  field
    preThingSingletonEqualityEvidence : PreThingSingletonEquality

  PreThingSingletonEquivalenceEvidence' : PreThingSingletonEquivalence
  PreThingSingletonEquivalenceEvidence' =
    equalToEquiv ∘ᶠ preThingSingletonEqualityEvidence
```

## The `Reality05` specification

The specification `record Reality05` adds the following mathematical abstraction.

- **Choices**: A material universe category *natural transformation* from a functor composed
with itself to to that functor composed with itself.

The specification `record Reality05` formalizes a pre-thing collection pre-interaction being
equal to the pre-interaction of the union, defined using the multiplication `μ` of a monad
structure on `CollFunctₘ`, of all choices of pre-things on the pre-thing collections of the
pre-thing collection pre-interaction. 

We import products (`_×_` from `Cubical.Data.Sigma`):

```agda
open import Cubical.Data.Sigma using (_×_)

record Choices
    {o m : Level}
    (C : Category o m)
    (F : Functor C C) :
  Type (lsuc (ℓ-max o m)) where

  field
    χ : NatTrans (F ∘F F) (F ∘F F)

open Choices {{...}} public

record Reality05 {o h : Level}
    (Catᵥ : Category o h)
    (Uᵥ : Category.ob Catᵥ)
    (Catₘ : Category o h)
    (CollFunctₘ : Functor Catₘ Catₘ)
    (Profunctₘᵥ : Profunctor⊶ o h Catₘ Catᵥ) :
  Type (lsuc (o ⊔ h)) where

  field
    reality04 : Reality04 Catᵥ Uᵥ Catₘ CollFunctₘ Profunctₘᵥ

  open Reality04 reality04 public

  field
    instance
      choicesₘ : Choices Catₘ CollFunctₘ

    preThingCollAsPreInteraction : Homₘ[ PreThingCollₘ , PreInteractionₘ ]

  PreThingCollPreInteraction≡UnionOfChoicesPreInteraction : Propertyₕ
  PreThingCollPreInteraction≡UnionOfChoicesPreInteraction =
    ∀ homₘ[1ₘ,CFₘ⟅PreThingCollₘ⟆]
    → let
        homₘ[1ₘ,PreThingCollₘ] = 
              homₘ[1ₘ,CFₘ⟅PreThingCollₘ⟆]
          ⋙ₘ CollFunctₘ ⟪ preThingCollAsCompositePreThing ⟫
        homₘ[1ₘ,PreThingCollₘ]' = 
              homₘ[1ₘ,CFₘ⟅PreThingCollₘ⟆]
          ⋙ₘ N-ob χ PreThingₘ
          ⋙ₘ N-ob (μ isMonadₘ) PreThingₘ
      in
          isPreInteraction homₘ[1ₘ,PreThingCollₘ]
        →   isPreInteraction homₘ[1ₘ,PreThingCollₘ]'
          × (   (homₘ[1ₘ,PreThingCollₘ] ⋙ₘ preThingCollAsPreInteraction)
              ≡ (homₘ[1ₘ,PreThingCollₘ]' ⋙ₘ preThingCollAsPreInteraction) )
```
