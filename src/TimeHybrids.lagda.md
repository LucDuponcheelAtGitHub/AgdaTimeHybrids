# Formalizing Fred Van Oystaeyen's "Time Hybrids"

This document presents a *formalization* of a *mathematical abstraction* of the *basics* of
Fred Van Oystaeyen's book, *Time Hybrids: A New Generic Theory of Reality*.

Fred, an outstanding mathematician, is a pioneer on *noncommutative algebraic geometry*. Among
others he wrote the book *Virtual topology and Functor geometry* that contributes to the
underlying mathematical abstraction of his *Time Hybrids: A New Generic Theory of Reality*
book.

Frankly, my mathematical abstraction is not be fully in sync with Fred's mathematical
abstraction in his *Virtual topology and Functor geometry* book.

My goal was to formalize the underlying mathematical abstraction of the basics of Fred's book
*computationally* in a *pointfree* way.

## Choices

There are two fundamental choices to be made.

### Mathematical Abstractions

*Please read diagonally if you are not inclined.* 

I *model* Fred's *Theory of Reality* using the following mathematical abstractions.

- **Categories**: Both the *virtual universe* and the *material universe* are modeled as
  categories. A category comes with *objects* and *homomorphisms* between objects.

- **Transitions**: *Dynamic evolution* is modeled as *transitions*, which are homomorphisms 
  from objects to theirselves (also called *endomorphisms*).

- **Functors**: The dynamic evolution of *universe objects* — such as *virtual pre-places* and 
  *material pre-thing collections* — is modeled using *functors* that map 
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
  Under the hood, structural induction computes directly using `transport` at path intervals.

- **Computational Univalence**: The *Univalence Principle* states that type equivalence
  (`_≃_`) is equivalent to type path equality (`_≡_`). In `Cubical Agda`, univalence computes
  natively via `ua` and `pathToEquiv`, allowing structural equivalences to be, well, equivalent
  to path equalities without needing unproven `postulate`s. Type path equality lives at a
  higher *type universe* level as type equivalence. Equivalence, `T₁ ≃ T₂`, looks *inside* the
  types at their elements while Equality `T₁­ ≡ T₂` looks *from above*, treating the types as
  elements of a higher (type) universe level.

Frankly, my choice for `Cubical Agda` is also motivated by *personal* preferences.
`Cubical Agda` is an academic effort, while `Lean 4` is an established effort sponsored by
important companies (you name them) and, as such, is also an industrial effort.  I know that
important results are achieved using `Lean 4`. I also know that Terence Tao recognizes
that `Cubical Agda`, based upon Homotopy Type Theory (HoTT), has advantages compored to
`Lean 4`. 

Below is some quote of Terence Tao.

*My own work does not interact with HoTT, but there are other areas of mathematics for which 
HOTT is a promising foundation. It isn't very well supported in `Lean 4` at the moment. My 
understanding is that Cubical Agda is currently the formal language that has the most support
for HOTT.* 

As far as I am concerned, the following is striking.

- **Harmonizing Paths and Transitions**: Category theory provides transitions **at** which
  state evolves. Homotopy Type Theory (HoTT) provides paths **at** which equality is
  structurally `transport`ed. In my formalization, these two concepts work in complete harmony.
  For example, path equalities between types are transported to path equalities between
  transition types. Note that I wrote *transitions at*, emphasising that, just as Fred, I
  consider *continous* transitions to be *discrete* entities. Similarly, note that I wrote
  *paths at*, emphasising that I consider *continuos* paths to be discrete entities. After all, 
  under the hood, they correspond to structural induction which is discrete.

### Why Profunctors matter

Profunctors,
see [nLab](https://ncatlab.org/nlab/show/profunctor)
and their `Cubical Agda` specification
see [Agda](https://github.com/agda/cubical/blob/master/Cubical/Categories/Profunctor/Base.agda)
turned out to be the natural abstraction to *formally separate* virtual universe related
concepts from material universe related concepts.

It is perfectly possible to go for other abstractions, but, as far as I know, they rely on
pre-places to belong to both the virtual universe and the material universe. As such they are,
in my opinion, sub-optimal abstractions.

Note that the *formalization* of the abstractions imposed pre-places to belong to both the
virtual universe and the material universe. I consider this as a formal "double-check" of
type systems, as the one of `Cubical Agda`, to inform you abot the consequences of the
abstraction choice you have made.

**All comments are welcome.**

## How the `Reality` abstraction is formalized incrementally

I am a mathematician. As such I am interested in the most simple general abstractions that
enabled me to formalize concepts of Fred's book as `Cubical Agda` specifications. Of course,
eventually, those abstractions and `Cubical Agda` specifications will become more complex.
Moreover, eventually, those abstractions and `Cubical Agda` specifications will become more
specific as (partial) concretions and (partial) `Cubical Agda` implementations respectively.

## Leveraging existing `Cubical Agda` modules as much as possible

We leverage standard libraries to keep `field` declarations and corresponding definitions
`Cubical Agda` idiomatic.

- Categories from `Cubical.Categories.Category.Base`.

- Functors from `Cubical.Categories.Functor.Base`.

- Profunctors from `Cubical.Categories.Profunctor.Base`.

So we `import` them to start with.

```agda
{-# OPTIONS --cubical --guardedness #-}

module TimeHybrids where

open import Agda.Primitive

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Profunctor.Base
```

## The `Reality01` specification

The specification `record Reality01` brings together the *virtual universe*, the
*material universe*, and how they *inter-act upon each other*.

### Parameters

`record Reality01` is parameterized by parameters

- `Cᵥ`: formalizing the *virtual universe category* with *virtual pre-places* (see later). The
  virtualuniverse is dynamic using *virtual universe transitions* (see later). Virtual
  pre-places are dynamic using *intra-functorially* corresponding 
  *virtual pre-place transitions* (see later).

- `Cₘ`: formalizing the *material universe category* with *material pre-thing collections*
  (see later). Material pre-thing collections are dynamic using *inter-functorially*
  corresponding *material pre-thing collection transitions* (see later).

and a parameter

- `PFₘᵥ`: formalizing the inter-action between the virtual universe and the material universe.

and a parameter:

- `CFₘ`: formalizing *to-collection mappings* in the material universe.

and parameters:

- `Uᵥ`: formalizing a unique designated virtual universe object that you can think of as the
  *state* of the virtual universe or, maybe more spectacular, as the *time* of the virtual
  universe. Virtual universe state/time transitions make the virtual universe dynamic. In
  what follows they are simpl referred to as virtual universe transitions. Viewing virtual
  universe dynamics as state changes focusses on the *consequence* of changes. Viewing virtual
  universe dynamics as time changes focusses on the *cause* of changes. But, really, both views
  are essentially equivalent.

- `Pₘ`: formalizing designated material objects, called *potentials*, being non-existing
*atomic pre-things* brewing what, eventually, may become *atomic existing things*.
Pre-thing collections can then be seen as being non-existing *composite pre-things* brewing
what, eventually, may become *composite existing things*.

Note that there are some *(implicit) `Level` parameters* involved. `o` for objects and `h` for
homomorphisms. They are necessary to avoid paradoxes that would occur when dealing with
theories in a naive way. Also note that `Reality01` itself has `Type` level `lsuc (o ⊔ h)`.
Reasoning about `Reality01` happens at a higher level.

```agda
record Reality01 {o h : Level}
    (Cᵥ : Category o h)
    (Cₘ : Category o h)
    (PFₘᵥ : Profunctor⊶ o h Cₘ Cᵥ)
    (CFₘ : Functor Cₘ Cₘ)
    (Uᵥ : Category.ob Cᵥ)
    (Pₘ : Category.ob Cₘ) :
  Type (lsuc (o ⊔ h)) where
```

The code below defines some, notationally convenient, renamings and synonyms. Technically, the
operation synonyms are introduced in order to be able to associate precedences with them.

```agda
  open Category Cᵥ renaming (ob to obᵥ; id to idᵥ; _∘_ to _∘ᵥ_)
  open Category Cₘ renaming (ob to obₘ; id to idₘ; _∘_ to _∘ₘ_)
  
  Homᵥ[_,_] : obᵥ → obᵥ → Type h
  Homᵥ[_,_] = Cᵥ [_,_]

  Homₘ[_,_] : obₘ → obₘ → Type h
  Homₘ[_,_] = Cₘ [_,_]

  open Profunctor⊶ PFₘᵥ

  Hetₘᵥ[_,_] : obₘ → obᵥ → Type h
  Hetₘᵥ[_,_] = Het[_,_]

  _ₗ∘_ : ∀ {Zₘ Yₘ : obₘ} {Xᵥ : obᵥ} → Homₘ[ Zₘ , Yₘ ] → Hetₘᵥ[ Yₘ , Xᵥ ] → Hetₘᵥ[ Zₘ , Xᵥ ]
  _ₗ∘_ = _⋆L_

  _∙ᵣ_ : ∀ {Zₘ : obₘ} {Yᵥ Xᵥ : obᵥ} → Hetₘᵥ[ Zₘ , Yᵥ ] → Homᵥ[ Yᵥ , Xᵥ ] → Hetₘᵥ[ Zₘ , Xᵥ ]
  _∙ᵣ_ = _⋆R_

  infixr 9 _ₗ∘_

  infixl 8 _∙ᵣ_
```

### `Functor` `field` declarations

- `prePlaceFunctorᵥ` formalizes mapping *virtual universe* transitions to *virtual pre-place*
   transitions, making pre-places dynamic. Note that only one category is involved.

- `preThingsFunctorᵥₘ` formalizes mapping *virtual universe* transitions to
  *material pre-thing collection* transitions, making pre-thing collections dynamic. Note that
  two categories are involved.


```agda
  field 
    prePlaceFunctorᵥ : Functor Cᵥ Cᵥ

    preThingsFunctorᵥₘ : Functor Cᵥ Cₘ
```

### Corresponding `obᵥ` and `obₘ` definitions

- `PrePlaceᵥ` is the `ob` (object) level part of `prePlaceFunctorᵥ` at `Uᵥ`, formalizing
  pre-places.

- `PreThingsᵥₘ` is the `ob` (object) level part of `preThingsFunctorᵥₘ` at `Uᵥ`, formalizing
  pre-thing collections.

```agda
  PrePlaceᵥ : obᵥ
  PrePlaceᵥ = prePlaceFunctorᵥ ⟅ Uᵥ ⟆

  PreThingsᵥₘ : obₘ
  PreThingsᵥₘ = preThingsFunctorᵥₘ ⟅ Uᵥ ⟆
```

### `obₘ` `field` declaration

- `PreThingₘ` formalizes material *pre-thing* objects. Recall that there are *atomic* and
  *composite* pre-things. For now we just declare `PreThingₘ`, leaving a definition for later.

```agda
  field
    PreThingₘ : obₘ
```

### Corresponding `obₘ` definition

- `PreThingsₘ` declares material *pre-thing collection* objects. You may argue that such objects
  have already been dealt with, being defined as `PreThingsᵥₘ`. The dynamic nature of pre-thing
  collections as `PreThingsᵥₘ` has been defined in terms of `preThingsFunctorᵥₘ`. Also the
  pre-place of a pre-thing collection will be been defined in terms of `preThingsFunctorᵥₘ`.
  Luckily the Cubical Homotopy Type Theory, on which `Cubical Agda` is based, can deal with all
  this and declare `PreThingsₘ` and `PreThingsᵥₘ` as equivalent, and, therefore, using
  univalence, as equal at a higher type universe level.

```agda
  PreThingsₘ : obₘ
  PreThingsₘ = CFₘ ⟅ PreThingₘ ⟆
```

### More `field` declarations

- `PreThingsᵥₘ≡PreThingsₘ` declares the equality of the previous subsection.

- `PreThingsₘ⊶PrePlaceᵥ` declares the *pre-thing collection pre-place* heteromorphism.

```agda  
  field
    PreThingsᵥₘ≡PreThingsₘ : PreThingsᵥₘ ≡ PreThingsₘ

    PreThingsₘ⊶PrePlaceᵥ : Hetₘᵥ[ PreThingsₘ , PrePlaceᵥ ]  
```

## Movement

We are ready to characterize *movement of pre-thing collections* in a dynamic universe and
corresponding universe pre-places setting. 

### `PrePlaceFunctorᵥ`

- `PrePlaceFunctorᵥ` specifies a virtual universe category functor `Fᵥ` that requires 
   equality of `Fᵥ ⟅ Uᵥ ⟆` with `PrePlaceᵥ` at `ob` level.

```agda
  record PrePlaceFunctorᵥ : Type (o ⊔ h) where
    constructor prePlaceFunctor
    pattern
    field
      Fᵥ : Functor Cᵥ Cᵥ
      Fᵥ⟅Uᵥ⟆≡PrePlaceᵥ : Fᵥ ⟅ Uᵥ ⟆ ≡ PrePlaceᵥ

  open PrePlaceFunctorᵥ
```

### `isMovementAtUniverseTransitionᵥ`

First we define a convenient local synonym `Property`. Note that the type universe level `h`
has been declared as an implicit `Level` typed parameter of `Reality01`. So it is a property
at homomorphism type universe level.

`isMovementAtUniverseTransitionᵥ` characterizes movement functorially as a `PrePlaceFunctorᵥ`
so that `movementTransitionᵥ`, defined in terms of it, equals `lhs` and `rhs` where

- `lhs` is the result of the left action of pre-thing collection transitions upon pre-thing
  collection pre-places
  
and 

- `rhs` is the result of the right action of pre-place transitions upon pre-thing collection
  pre-places

by 

- letting the movement transition right act upon `rhs`.

```agda
  Property = Type h

  isMovementAtUniverseTransitionᵥ : PrePlaceFunctorᵥ → Homᵥ[ Uᵥ , Uᵥ ] → Property
  isMovementAtUniverseTransitionᵥ (prePlaceFunctor Fᵥ Fᵥ⟅Uᵥ⟆≡PrePlaceᵥ) universeTransitionᵥ =
    let prePlaceTransitionᵥ = prePlaceFunctorᵥ ⟪ universeTransitionᵥ ⟫  
        preThingsTransitionᵥₘ = preThingsFunctorᵥₘ ⟪ universeTransitionᵥ ⟫
        preThingsTransitionₘ : Homₘ[ PreThingsᵥₘ≡PreThingsₘ i1 , PreThingsᵥₘ≡PreThingsₘ i1 ]
        preThingsTransitionₘ =
          transp 
            (λ (i : I) → Homₘ[ PreThingsᵥₘ≡PreThingsₘ i , PreThingsᵥₘ≡PreThingsₘ i ])
            i0
            preThingsTransitionᵥₘ
        movementTransitionᵥ : Homᵥ[ Fᵥ⟅Uᵥ⟆≡PrePlaceᵥ i1 , Fᵥ⟅Uᵥ⟆≡PrePlaceᵥ i1 ]
        movementTransitionᵥ =
          transp
            (λ (i : I) → Homᵥ[ Fᵥ⟅Uᵥ⟆≡PrePlaceᵥ i , Fᵥ⟅Uᵥ⟆≡PrePlaceᵥ i ])
            i0
            (Fᵥ ⟪ universeTransitionᵥ ⟫)
        lhs = preThingsTransitionₘ ₗ∘ PreThingsₘ⊶PrePlaceᵥ
        rhs = PreThingsₘ⊶PrePlaceᵥ ∙ᵣ prePlaceTransitionᵥ
    in lhs ∙ᵣ movementTransitionᵥ ≡ rhs
```

Note how naturally Homotopy Type Theory deals with defining

- pre-thing collection transition equality in terms of pre-thing collection equality.

and 

- movement transitions in terms of `Fᵥ⟅Uᵥ⟆` and `PrePlaceᵥ` equality at the `ob` level.

### `isImmobileAtUniverseTransitionᵥ`

Characterising *immobility* is now also easy and simple by using a *constant* virtual pre-place
functor `Constant Cᵥ Cᵥ PrePlaceᵥ` that *definitionally* (using `refl` evidence), deals with
`PrePlaceᵥ`s at the `ob` level. 

```agda
  open import Cubical.Categories.Functors.Constant

  isImmobileAtUniverseTransitionᵥ : Homᵥ[ Uᵥ , Uᵥ ] → Property
  isImmobileAtUniverseTransitionᵥ =
    isMovementAtUniverseTransitionᵥ (prePlaceFunctor (Constant Cᵥ Cᵥ PrePlaceᵥ) refl)
```


