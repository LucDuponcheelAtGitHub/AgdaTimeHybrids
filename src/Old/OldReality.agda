{-# OPTIONS --cubical --guardedness #-}

module OldReality where

open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to ℓ-max)

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Unit
  using (Unit; tt; isSetUnit; isPropUnit; Unit*; tt*; isSetUnit*; isPropUnit*)
open import Cubical.Categories.Limits.Terminal
  using (Terminal; terminalOb; isTerminal; terminalArrow; terminalArrowUnique)


open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Foundations.Equiv using (_≃_; invEquiv)
open import Cubical.Foundations.Univalence
  using (ua; pathToEquiv; univalence; ua-pathToEquiv; pathToEquiv-ua)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Foundations.HLevels
  using (isPropΠ; isPropΠ2; isProp→; isProp×; isSet×; isSetRetract)

open import Cubical.Categories.Category.Base using (Category; _[_,_])
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.Functor.Base as CubicalFunctor
  using (Functor; _⟅_⟆; _⟪_⟫; Id; _∘F_)
open import Cubical.Categories.Functor.Properties
  using (F-rUnit; F-lUnit; F-assoc)
open import Cubical.Categories.Monad.Base
  using (IsMonad)
open import Cubical.Categories.NaturalTransformation.Base
  using (NatTrans; idTrans; makeNatTransPathP)
open import Cubical.Categories.Profunctor.Base
  using (Profunctor⊶; module Profunctor⊶)

open import Cubical.Relation.Binary.Order.Proset
  using (ProsetStr; module ProsetStr; IsProset; module IsProset; prosetstr)

open Category hiding (_∘_)

open NatTrans

open IsMonad

open ProsetStr {{...}} public

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


transformationMorphism :
  ∀ {o₁ m₁ o₂ m₂} {C : Category o₁ m₁} {D : Category o₂ m₂}
    {F G : Functor C D}
  → NatTrans F G
  → ∀ (Z : ob C) → D [ F ⟅ Z ⟆ , G ⟅ Z ⟆ ]
transformationMorphism = N-ob

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

record Supremum
    {o m : Level}
    (C : Category o m)
    (CF : Functor C C)
    (Z : Category.ob C) :
      Type (lsuc (ℓ-max o m)) where
  field
    supremum : C [ CF ⟅ Z ⟆ , Z ]

open Supremum {{...}} public

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

  field
    preThingCollectionPathEquality :
      preThingCollectionFunctor ⟅ Uᵥ ⟆ ≡ PreThingCollection

    isGlobalPreThingSingleton :
      GlobalPreThingCollection → Type m

    isGlobalPreInteraction :
      GlobalPreThingCollection → Type m

    preThingCollectionAsPreThingMorphism :
      Cₘ [ PreThingCollection , PreThing ]

    preThingCollectionAsPreInteractionMorphism :
      Cₘ [ PreThingCollection , PreInteraction ]

    preThingCollectionPrePlaceHeteroMorphism :
      PreThingCollectionPrePlaceHeteroMorphism

    preThingSingletonPrePlaceHeteroMorphismLift :
      PreThingCollectionPrePlaceHeteroMorphism →
        PreThingSingletonCollectionPrePlaceCollectionHeteromorphism

    instance
      universeTransitionProsetStr :
        ProsetStr m UniverseTransition

      globalPreThingCollectionProsetStr :
        ProsetStr m GlobalPreThingCollection

      globalHeteroPrePlaceProsetStr :
        ProsetStr m GlobalHeteroPrePlace

      prePlaceMorphismSupremum :
        Supremum Cᵥ CFᵥ PrePlace

  universeTransitionToPrePlaceTransition :
    UniverseTransition → PrePlaceTransition
  universeTransitionToPrePlaceTransition universeTransition =
    prePlaceFunctor ⟪ universeTransition ⟫

  universeTransitionToPreThingCollectionFunctorTransition :
    UniverseTransition → PreThingCollectionFunctorTransition
  universeTransitionToPreThingCollectionFunctorTransition =
    λ universeTransition →
      preThingCollectionFunctor ⟪ universeTransition ⟫

  materialTransitionPathEqualityLifter :
    {Z Y : obₘ} → Z ≡ Y → Cₘ [ Z , Z ] ≡ Cₘ [ Y , Y ]
  materialTransitionPathEqualityLifter z≡y =
    λ i → Cₘ [ z≡y i , z≡y i ]

  preThingCollectionTransitionPathEquality :
    PreThingCollectionFunctorTransition ≡ PreThingCollectionTransition
  preThingCollectionTransitionPathEquality =
    materialTransitionPathEqualityLifter preThingCollectionPathEquality

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

  preThingCollectionCollectionAsPreThingCollectionMorphism :
    Cₘ [ PreThingCollectionCollection , PreThingCollection ]
  preThingCollectionCollectionAsPreThingCollectionMorphism =
    CFₘ ⟪ preThingCollectionAsPreThingMorphism ⟫

  preThingCollectionCollectionAsPreInteractionMorphism :
    Cₘ [ PreThingCollectionCollection , PreInteraction ]
  preThingCollectionCollectionAsPreInteractionMorphism =
    preThingCollectionCollectionAsPreThingCollectionMorphism ⋙ₘ
      preThingCollectionAsPreInteractionMorphism

  isGlobalPreThingSingletonInteraction :
    GlobalPreThingCollection → Type m
  isGlobalPreThingSingletonInteraction globalPreThingCollection =
    isGlobalPreThingSingleton globalPreThingCollection ×
      isGlobalPreInteraction globalPreThingCollection

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

  ChoicesToPreThingCollectionCollectionUnionAbsorption : Type m
  ChoicesToPreThingCollectionCollectionUnionAbsorption =
    (choicesTransformationTransition ⋙ₘ unionTransformationMorphism) ≡
      unionTransformationMorphism

  choicesToPreThingCollectionCollectionUnionAbsorption :
    ChoicesToPreThingCollectionCollectionUnionAbsorption
  choicesToPreThingCollectionCollectionUnionAbsorption = choices-union-absorption

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
                -- doubleNestedSingletonTransformationMorphism ⋙ₘ
                --   nestedUnionTransformationMorphism ⋙ₘ
                    preThingCollectionCollectionAsPreInteractionMorphism
      in isGlobalPreInteraction globalPreThingCollection →
          globalPreInteraction ≡ globalPreInteraction'

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

--------------------------------------------------------------------------------
-- MaterialUniverse Implementation: SET₀ with LFSet
--------------------------------------------------------------------------------

open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.HITs.ListedFiniteSet.Base as LFS
  using (LFSet; trunc; _++_)
  renaming ([] to []S; _∷_ to _∷S_)
open import Cubical.HITs.ListedFiniteSet.Properties as LFSP

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

--------------------------------------------------------------------------------
-- Recursive Compositional Structure: PreThingTree
--------------------------------------------------------------------------------

data PreThingTree (Z : Type lzero) : Type lzero where
  atomic            : Z → PreThingTree Z
  composite         : LFSet (PreThingTree Z) → PreThingTree Z
  truncPreThingTree : isSet (PreThingTree Z)

PreThingTree-isSet : ∀ {Z : Type lzero} → isSet (PreThingTree Z)
PreThingTree-isSet = truncPreThingTree

--------------------------------------------------------------------------------
-- Partial Implementation of Reality and PreOrderedReality for MaterialUniverse = SET₀

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
