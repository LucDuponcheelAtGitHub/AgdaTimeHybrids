{-# OPTIONS --cubical --guardedness #-}

module Reality where

open import Agda.Primitive

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Profunctor.Base

record Reality01 {o h : Level}
    (Cᵥ : Category o h)
    (Cₘ : Category o h)
    (PFₘᵥ : Profunctor⊶ o h Cₘ Cᵥ)
    (CFₘ : Functor Cₘ Cₘ)
    (Uᵥ : Category.ob Cᵥ)
    (Pₘ : Category.ob Cₘ) :
  Type (lsuc (o ⊔ h)) where

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

  field 
    prePlaceFunctorᵥ : Functor Cᵥ Cᵥ

    preThingsFunctorᵥₘ : Functor Cᵥ Cₘ

  PrePlaceᵥ : obᵥ
  PrePlaceᵥ = prePlaceFunctorᵥ ⟅ Uᵥ ⟆

  PreThingsᵥₘ : obₘ
  PreThingsᵥₘ = preThingsFunctorᵥₘ ⟅ Uᵥ ⟆

  field
    PreThingₘ : obₘ

  PreThingsₘ : obₘ
  PreThingsₘ = CFₘ ⟅ PreThingₘ ⟆
  
  field
    PreThingsᵥₘ≡PreThingsₘ : PreThingsᵥₘ ≡ PreThingsₘ

    PreThingsₘ⊶PrePlaceᵥ : Hetₘᵥ[ PreThingsₘ , PrePlaceᵥ ]  

  record PrePlaceFunctorᵥ : Type (o ⊔ h) where
    constructor prePlaceFunctor
    pattern
    field
      Fᵥ : Functor Cᵥ Cᵥ
      Fᵥ⟅Uᵥ⟆≡PrePlaceᵥ : Fᵥ ⟅ Uᵥ ⟆ ≡ PrePlaceᵥ

  open PrePlaceFunctorᵥ

  Property = Type h

  isMovementAtUniverseTransitionᵥ : PrePlaceFunctorᵥ → Homᵥ[ Uᵥ , Uᵥ ] → Property
  isMovementAtUniverseTransitionᵥ (prePlaceFunctor Fᵥ Fᵥ⟅Uᵥ⟆≡PrePlaceᵥ) universeTransitionᵥ =
    let 
      prePlaceTransitionᵥ = prePlaceFunctorᵥ ⟪ universeTransitionᵥ ⟫  
      preThingsTransitionᵥₘ = preThingsFunctorᵥₘ ⟪ universeTransitionᵥ ⟫
      preThingsTransitionₘ : Homₘ[ PreThingsₘ , PreThingsₘ ]
      preThingsTransitionₘ =
        transp 
          (λ (i : I) → Homₘ[ PreThingsᵥₘ≡PreThingsₘ i , PreThingsᵥₘ≡PreThingsₘ i ])
          i0
          preThingsTransitionᵥₘ
      movementTransitionᵥ : Homᵥ[ PrePlaceᵥ , PrePlaceᵥ ]
      movementTransitionᵥ =
        transp
          (λ (i : I) → Homᵥ[ Fᵥ⟅Uᵥ⟆≡PrePlaceᵥ i , Fᵥ⟅Uᵥ⟆≡PrePlaceᵥ i ])
          i0
          (Fᵥ ⟪ universeTransitionᵥ ⟫)
      lhs : Hetₘᵥ[ PreThingsₘ , PrePlaceᵥ ]    
      lhs = preThingsTransitionₘ ₗ∘ PreThingsₘ⊶PrePlaceᵥ
      rhs : Hetₘᵥ[ PreThingsₘ , PrePlaceᵥ ]
      rhs = PreThingsₘ⊶PrePlaceᵥ ∙ᵣ prePlaceTransitionᵥ
    in 
      lhs ∙ᵣ movementTransitionᵥ ≡ rhs

  open import Cubical.Categories.Functors.Constant

  isImmobileAtUniverseTransitionᵥ : Homᵥ[ Uᵥ , Uᵥ ] → Property
  isImmobileAtUniverseTransitionᵥ =
    isMovementAtUniverseTransitionᵥ (prePlaceFunctor (Constant Cᵥ Cᵥ PrePlaceᵥ) refl)


open import Cubical.Categories.Limits.Terminal

record Reality02 {o h : Level}
    (Cᵥ : Category o h)
    (Cₘ : Category o h)
    (PFₘᵥ : Profunctor⊶ o h Cₘ Cᵥ)
    (CFₘ : Functor Cₘ Cₘ)
    (Uᵥ : Category.ob Cᵥ)
    (Pₘ : Category.ob Cₘ) :  
  Type (lsuc (o ⊔ h)) where

  open Category Cₘ renaming (ob to obₘ; id to idₘ; _∘_ to _∘ₘ_)

  field
    reality01 : Reality01 Cᵥ Cₘ PFₘᵥ CFₘ Uᵥ Pₘ

  open Reality01 reality01 public
  
  field
    terminalₘ : Terminal Cₘ

  1ₘ : obₘ
  1ₘ = terminalOb Cₘ terminalₘ
  
  PreInteractionₘ : obₘ
  PreInteractionₘ = PreThingsₘ 

  field 
    isGlobalPreInteractionₘ : Homₘ[ 1ₘ , PreThingsₘ ] → Property 

  _⋙ₘ_ : ∀ {Z Y X : obₘ} → Homₘ[ Z , Y ] → Homₘ[ Y , X ] → Homₘ[ Z , X ]
  f ⋙ₘ g = g ∘ₘ f

  infixl 8 _⋙ₘ_

  preThingsTransitionᵥₘToPreThingsTransitionₘAt :
    Homᵥ[ Uᵥ , Uᵥ ] → Homₘ[ PreThingsₘ , PreThingsₘ ]
  preThingsTransitionᵥₘToPreThingsTransitionₘAt =
    λ universeTransitionᵥ →
      let
        preThingsTransitionᵥₘ = preThingsFunctorᵥₘ ⟪ universeTransitionᵥ ⟫
      in 
        transport
          (λ i → Homₘ[ PreThingsᵥₘ≡PreThingsₘ i , PreThingsᵥₘ≡PreThingsₘ i ])
          preThingsTransitionᵥₘ      

  PreInteractionPreservation : Property
  PreInteractionPreservation =
    ∀ (universeTransitionᵥ : Homᵥ[ Uᵥ , Uᵥ ]) 
      (globalPreThingsₘ : Homₘ[ 1ₘ , PreThingsₘ ])
    → let 
        preThingsTransitionₘ =
          preThingsTransitionᵥₘToPreThingsTransitionₘAt universeTransitionᵥ
      in 
        isGlobalPreInteractionₘ globalPreThingsₘ 
        → isGlobalPreInteractionₘ (globalPreThingsₘ ⋙ₘ preThingsTransitionₘ)

open import Cubical.Categories.NaturalTransformation.Base

open NatTrans

record Zero
    {o h : Level}
    (C : Category o h)
    (F : Functor C C) :
  Type (lsuc (ℓ-max o h)) where

  open Category C -- renaming (_∘_ to _∘C_)

  field
    ζ : NatTrans F F

  zero : (Z : Category.ob C) → C [ F ⟅ Z ⟆ , F ⟅ Z ⟆ ]
  zero = N-ob ζ

  field
    zero-absorption :
      ∀ {Z : Category.ob C}
        (f : C [ F ⟅ Z ⟆ , F ⟅ Z ⟆ ])
      → f ∘ zero Z ≡ zero Z

open Zero {{...}} public

record Reality03 {o h : Level}
    (Cᵥ : Category o h)
    (Cₘ : Category o h)
    (PFₘᵥ : Profunctor⊶ o h Cₘ Cᵥ)
    (CFₘ : Functor Cₘ Cₘ)
    (Uᵥ : Category.ob Cᵥ)
    (Pₘ : Category.ob Cₘ) :  
  Type (lsuc (o ⊔ h)) where

  field
    reality02 : Reality02 Cᵥ Cₘ PFₘᵥ CFₘ Uᵥ Pₘ

  open Reality02 reality02 public
 
  field
    instance
      nothingₘ : Zero Cₘ CFₘ
  
  toNothingTransitionₘ : Homₘ[ PreThingsₘ , PreThingsₘ ]
  toNothingTransitionₘ = N-ob (ζ ⦃ nothingₘ ⦄) PreThingₘ

  NoEscapeFromNothingₘ : Property
  NoEscapeFromNothingₘ =
    ∀ universeTransitionᵥ
    → let 
        preThingsTransitionₘ =
          preThingsTransitionᵥₘToPreThingsTransitionₘAt universeTransitionᵥ
      in 
        toNothingTransitionₘ ⋙ₘ preThingsTransitionₘ ≡ toNothingTransitionₘ

  noEscapeFromNothingProofₘ : NoEscapeFromNothingₘ
  noEscapeFromNothingProofₘ =
    λ universeTransitionᵥ →
      let 
        preThingsTransitionₘ =
          preThingsTransitionᵥₘToPreThingsTransitionₘAt universeTransitionᵥ
      in
        zero-absorption preThingsTransitionₘ

-----------------------------------------------------------------------------------------------

open import Agda.Builtin.Cubical.Equiv

open import Cubical.Categories.Monad.Base

open IsMonad

record Reality04 {o h : Level}
    (Cᵥ : Category o h)
    (Cₘ : Category o h)
    (PFₘᵥ : Profunctor⊶ o h Cₘ Cᵥ)
    (CFₘ : Functor Cₘ Cₘ)
    (Uᵥ : Category.ob Cᵥ)
    (Pₘ : Category.ob Cₘ) :  
  Type (lsuc (o ⊔ h)) where

  open Category Cₘ renaming (ob to obₘ; id to idₘ; _∘_ to _∘ₘ_)

  field
    reality03 : Reality03 Cᵥ Cₘ PFₘᵥ CFₘ Uᵥ Pₘ

    instance
      isMonadₘ : IsMonad CFₘ

  open Reality03 reality03 public

  field
    isGlobalPreThingSingletonₘ : Homₘ[ 1ₘ , PreThingsₘ ] → Property 

    preThingsAsPreThingₘ : Homₘ[ PreThingsₘ , PreThingₘ ]

  PreThingSingletonₘ : obₘ
  PreThingSingletonₘ = PreThingsₘ

  preThingToPreThingSingletonₘ : Homₘ[ PreThingₘ , PreThingSingletonₘ ]
  preThingToPreThingSingletonₘ = N-ob (η isMonadₘ) PreThingₘ

  PreThingSingletonEquivalenceₘ : Property
  PreThingSingletonEquivalenceₘ =
    (globalPreThingsₘ : Homₘ[ 1ₘ , PreThingsₘ ])
    → isGlobalPreThingSingletonₘ globalPreThingsₘ ≃
        (globalPreThingsₘ ≡
          globalPreThingsₘ ⋙ₘ preThingsAsPreThingₘ ⋙ₘ preThingToPreThingSingletonₘ)

  -- preThingssAsPreThingsₘ : Homₘ[ CFₘ ⟅ (CFₘ ⟅ PreThingsₘ ⟆) ⟆ , CFₘ ⟅ PreThingsₘ ⟆ ]
  preThingssAsPreThingsₘ = CFₘ ⟪ preThingsAsPreThingₘ ⟫

-- record Choices
--     {o m : Level}
--     (C : Category o m)
--     (F : Functor C C)
--     (isMonad : IsMonad F) :
--   Type (lsuc (ℓ-max o m)) where

--   open Category C renaming (id to idC; _∘_ to _∘C_)

--   union : (Z : Category.ob C) → C [ (F ∘F F) ⟅ Z ⟆ , F ⟅ Z ⟆ ]
--   union = N-ob (μ isMonad)

--   field
--     χ : NatTrans (F ∘F F) (F ∘F F)

--   choices : (Z : Category.ob C) → C [ (F ∘F F) ⟅ Z ⟆ , (F ∘F F) ⟅ Z ⟆ ]
--   choices = N-ob χ

--   field
--     choices-union-absorption :
--       ∀ {Z : Category.ob C}
--       → union Z ∘C choices Z ≡ union Z

-- open Choices {{...}} public

  -- preInteractionCollectionAsUnionOfSingletonsOfChoicesPreInteractions : Type m
  -- preInteractionCollectionAsUnionOfSingletonsOfChoicesPreInteractions =
  --   (globalPreThingss :
  --       CFₘ ⟅ CFₘ ⟅ PreThingsₘ ⟆ ⟆ )
  --   → let globalPreThingCollection =
  --           globalPreThingss ⋙ₘ
  --             preThingssAsPreThingCollectionMorphism
  --         globalPreInteraction =
  --           globalPreThingCollection ⋙ₘ
  --             preThingCollectionAsPreInteractionMorphism
  --         globalPreInteraction' =
  --           globalPreThingss ⋙ₘ
  --             choicesTransformationTransition ⋙ₘ
  --               doubleNestedSingletonTransformationMorphism ⋙ₘ
  --                 nestedUnionTransformationMorphism ⋙ₘ
  --                   preThingssAsPreInteractionMorphism
  --     in isGlobalPreInteraction globalPreThingCollection →
  --         globalPreInteraction ≡ globalPreInteraction'


-- open import Cubical.Categories.Monad.Base

-- record Choices
--     {o h : Level}
--     (C : Category o h)
--     (F : Functor C C)
--     (M : IsMonad F) :
--   Type (lsuc (o ⊔ h)) where

--   open Category C 

--   open IsMonad

--   union : (Z : Category.ob C) → C [ (F ∘F F) ⟅ Z ⟆ , F ⟅ Z ⟆ ]
--   union = NatTrans.N-ob (μ M)

--   field
--     χ : NatTrans (F ∘F F) (F ∘F F)

--   choices : (Z : Category.ob C) → C [ (F ∘F F) ⟅ Z ⟆ , (F ∘F F) ⟅ Z ⟆ ]
--   choices = NatTrans.N-ob χ

--   field
--     choices-union-absorption :
--       ∀ {Z : Category.ob C}
--       → union Z ∘ choices Z ≡ union Z

-- open Choices