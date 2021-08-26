{-# OPTIONS --cubical --no-import-sorts --safe #-}

module SmallSubtypes.Container where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_; I to I′)

private
  variable
    i o c r i₂ o₂ c₂ r₂ ℓ₁ ℓ₂ : Level
    I : Type i
    O : Type o
    I₂ : Type i₂
    O₂ : Type o₂


-- Definition of indexed containers from the Agda standard library

record Container (I : Type i) (O : Type o) (c r : Level) :
                 Type (i ⊔ o ⊔ ℓ-suc c ⊔ ℓ-suc r) where
  constructor _◃_/_
  field
    Command  : (o : O) → Type c
    Response : ∀ {o} → Command o → Type r
    next     : ∀ {o} (c : Command o) → Response c → I

⟦_⟧ : Container I O c r → (I → Type ℓ₁) → O → Type _
⟦ C ◃ R / n ⟧ X o = Σ[ c ∈ C o ] ((r : R c) → X (n c r))

⟦_⟧₂ : Container I O c r → (A : I → Type ℓ₁) → (B : {i : I} → A i → Type ℓ₂) → O → Type _
⟦ C ◃ R / n ⟧₂ A B o = Σ[ (c , f) ∈ ⟦ C ◃ R / n ⟧ A o ] ((r : R c) → B (f r))

-- Indexed container morphisms

open Container

record Morphism {I₁ : Type i} {I₂ : Type i₂} {O₁ : Type o} {O₂ : Type o₂}
                (In : I₁ → I₂) (Out : O₁ → O₂)
                (C₁ : Container I₁ O₁ c r) (C₂ : Container I₂ O₂ c₂ r₂)
                : Type (i ⊔ o ⊔ i₂ ⊔ o₂ ⊔ c ⊔ r ⊔ c₂ ⊔ r₂) where
  field
    Com : ∀ o → Command C₁ o → Command C₂ (Out o)
    Res : ∀ {o} c → Response C₂ (Com o c) → Response C₁ c
    Coh : ∀ {o} (c : Command C₁ o) r →
            In (next C₁ c (Res c r)) ≡ next C₂ (Com o c) r

open Morphism

_⇒ⁱ_ : (C₁ : Container I O c r) (C₂ : Container I₂ O₂ c₂ r₂) → Type _
_⇒ⁱ_ {I = I} {O = O} {I₂ = I₂} {O₂ = O₂} C₁ C₂ =
  Σ[ f ∈ (I → I₂) ] Σ[ g ∈ (O → O₂) ] Morphism f g C₁ C₂

⟪_⟫ⁱ : {C₁ : Container I O c r} {C₂ : Container I₂ O₂ c₂ r₂} →
      ((In , Out , f) : C₁ ⇒ⁱ C₂) (B : I₂ → Type ℓ₁) → ∀ {o} →
      ⟦ C₁ ⟧ (B ∘ In) o → ⟦ C₂ ⟧ B (Out o)
⟪ (In , Out , f) ⟫ⁱ B (s , g) = Com f _ s , subst B (Coh f _ _) ∘ g ∘ Res f s

_⇒_ : (C₁ : Container I O c r) (C₂ : Container I O c₂ r₂) → Type _
C₁ ⇒ C₂ = Morphism (λ x → x) (λ x → x) C₁ C₂

⟪_⟫ : {C₁ : Container I O c r} {C₂ : Container I O c₂ r₂} →
      C₁ ⇒ C₂ → (B : I → Type ℓ₁) → ∀ {o} → ⟦ C₁ ⟧ B o → ⟦ C₂ ⟧ B o
⟪ f ⟫ B (s , g) = Com f _ s , subst B (Coh f _ _) ∘ g ∘ Res f s

map : (C : Container I O c r) {A : I → Type ℓ₁} {B : I → Type ℓ₂} →
      (∀ {i} → A i → B i) → ∀ o → ⟦ C ⟧ A o → ⟦ C ⟧ B o
map C f o (s , g) = s , f ∘ g
