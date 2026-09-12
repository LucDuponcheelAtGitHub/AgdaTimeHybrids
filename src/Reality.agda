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

  record MovementFunctorᵥ : Type (o ⊔ h) where
    constructor movementFunctorᵥ
    pattern
    field
      Fᵥ : Functor Cᵥ Cᵥ
      Fᵥ⟅Uᵥ⟆≡PrePlaceᵥ : Fᵥ ⟅ Uᵥ ⟆ ≡ PrePlaceᵥ

  open MovementFunctorᵥ

  Property = Type h

  isMovementAtUniverseTransitionᵥ : MovementFunctorᵥ → Homᵥ[ Uᵥ , Uᵥ ] → Property
  isMovementAtUniverseTransitionᵥ (movementFunctorᵥ Fᵥ Fᵥ⟅Uᵥ⟆≡PrePlaceᵥ) universeTransitionᵥ =
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
    in preThingsTransitionₘ ₗ∘ PreThingsₘ⊶PrePlaceᵥ ∙ᵣ movementTransitionᵥ ≡
       PreThingsₘ⊶PrePlaceᵥ ∙ᵣ prePlaceTransitionᵥ

  open import Cubical.Categories.Functors.Constant

  isImmobileAtUniverseTransitionᵥ : Homᵥ[ Uᵥ , Uᵥ ] → Property
  isImmobileAtUniverseTransitionᵥ =
    isMovementAtUniverseTransitionᵥ (movementFunctorᵥ (Constant Cᵥ Cᵥ PrePlaceᵥ) refl)

-----------------------------------------------------------------------------------------------

    -- (CFᵥ : Functor Cᵥ Cᵥ) -- not needed yet

--   _⋙ᵥ_ : ∀ {Z Y X : obᵥ} → Cᵥ [ Z , Y ] → Cᵥ [ Y , X ] → Cᵥ [ Z , X ]
--   f ⋙ᵥ g = g ∘ᵥ f

--   _⋙ₘ_ : ∀ {Z Y X : obₘ} → Cₘ [ Z , Y ] → Cₘ [ Y , X ] → Cₘ [ Z , X ]
--   f ⋙ₘ g = g ∘ₘ f

--   infixl 8 _⋙ᵥ_

--   infixl 8 _⋙ₘ_


--   field  -- not needed yet
--     potentialAsAtomicPreThingₘ : Cₘ [ Pₘ , PreThingₘ ]  -- not needed yet

--     preThingsAsCompositePreThingₘ : Cₘ [ PreThingsₘ , PreThingₘ ]  -- not needed yet

-- record Zero
--     {o h : Level}
--     (C : Category o h)
--     (F : Functor C C) :
--   Type (lsuc (o ⊔ h)) where

--   open Category C

--   field
--     ζ : NatTrans F F

--   zero : (Z : Category.ob C) → C [ F ⟅ Z ⟆ , F ⟅ Z ⟆ ]
--   zero = NatTrans.N-ob ζ

--   field
--     zero-absorption :
--       ∀ {Z : Category.ob C}
--         (h : C [ F ⟅ Z ⟆ , F ⟅ Z ⟆ ])
--       → h ∘ zero Z ≡ zero Z

-- open Zero

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