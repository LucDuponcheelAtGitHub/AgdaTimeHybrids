{-# OPTIONS --cubical --guardedness #-}

module Reality where

open import Agda.Primitive

open import Agda.Builtin.Cubical.Equiv

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function renaming (_∘_ to _∘ᶠ_)
open import Cubical.Foundations.Univalence 
  renaming (ua to equivToEqual; pathToEquiv to equalToEquiv)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Profunctor.Base
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Monad.Base

open import Cubical.Data.Sigma using (_×_)

open NatTrans

open IsMonad

record Reality01 {o h : Level}
    (Catᵥ : Category o h)
    (Uᵥ : Category.ob Catᵥ)
    (Catₘ : Category o h)
    (CollFunctₘ : Functor Catₘ Catₘ)
    (Profunctₘᵥ : Profunctor⊶ o h Catₘ Catᵥ) :
  Type (lsuc (o ⊔ h)) where

  Propertyₕ = Type h

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

  _⋙ᵥ_ : ∀ {Z Y X : obᵥ} → Homᵥ[ Z , Y ] → Homᵥ[ Y , X ] → Homᵥ[ Z , X ]
  f ⋙ᵥ g = g ∘ᵥ f

  infixl 8 _⋙ᵥ_

  _⋙ₘ_ : ∀ {Z Y X : obₘ} → Homₘ[ Z , Y ] → Homₘ[ Y , X ] → Homₘ[ Z , X ]
  f ⋙ₘ g = g ∘ₘ f

  infixl 8 _⋙ₘ_

  open Profunctor⊶ Profunctₘᵥ

  Hetₘᵥ[_,_] : obₘ → obᵥ → Type h
  Hetₘᵥ[_,_] = Het[_,_]

  _ₗ∘_ : ∀ {Zₘ Yₘ : obₘ} {Xᵥ : obᵥ} → Homₘ[ Zₘ , Yₘ ] → Hetₘᵥ[ Yₘ , Xᵥ ] → Hetₘᵥ[ Zₘ , Xᵥ ]
  _ₗ∘_ = _⋆L_

  infixl 9 _ₗ∘_

  _∙ᵣ_ : ∀ {Zₘ : obₘ} {Yᵥ Xᵥ : obᵥ} → Hetₘᵥ[ Zₘ , Yᵥ ] → Homᵥ[ Yᵥ , Xᵥ ] → Hetₘᵥ[ Zₘ , Xᵥ ]
  _∙ᵣ_ = _⋆R_

  infixr 8 _∙ᵣ_

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

  record PrePlaceFunctor : Type (o ⊔ h) where
    constructor ppf
    pattern
    field
      functor : Functor Catᵥ Catᵥ
      functor⟅Uᵥ⟆≡PrePlaceᵥ : functor ⟅ Uᵥ ⟆ ≡ PrePlaceᵥ

  open PrePlaceFunctor

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

  noMovementFunctor : PrePlaceFunctor
  noMovementFunctor = ppf (Constant Catᵥ Catᵥ PrePlaceᵥ) refl

  isImmobileAt : Transᵥ[ Uᵥ ] → Propertyₕ
  isImmobileAt transᵥ[Uᵥ] = noMovementFunctor isMovementAt transᵥ[Uᵥ]

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
