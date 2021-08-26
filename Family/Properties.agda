{-# OPTIONS --cubical --no-import-sorts --safe #-}

module SmallSubtypes.Family.Properties where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_; I to I′)

open import SmallSubtypes.Container
open import SmallSubtypes.Family.Base

private
  variable
    i o c r i₂ o₂ c₂ r₂ ℓ₁ ℓ₂ : Level
    I : Type i
    O : Type o
    I₂ : Type i₂
    O₂ : Type o₂

open Iso

FreePMIso : (C : Container O O c r) (P : O → Type ℓ₁) →
            (∀ o → isProp (P o)) → (∀ o → ⟦ C ⟧ P o → P o) →
            ∀ o → Iso (FreePM C P o) (P o)
fun      (FreePMIso C P isPropP α o)   = recFreePM P isPropP (λ _ x → x) α
inv      (FreePMIso C P isPropP α o)   = η o
rightInv (FreePMIso C P isPropP α o) _ = refl
leftInv  (FreePMIso C P isPropP α o) _ = squash _ _ _

