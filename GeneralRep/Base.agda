{-# OPTIONS --cubical --no-import-sorts --safe #-}

module SmallSubtypes.GeneralRep.Base where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)

open import SmallSubtypes.Fiber
open import SmallSubtypes.Container

open Container
open Iso
  
module _ {ℓ₁ c r ℓ₂ : Level} {O : Type ℓ₁} (C : Container O O c r)
         (A : O → Type ℓ₂) (α : (o : O) → ⟦ C ⟧ A o → A o)  where

  private
    variable
      o : O

  data RepFam : O → Type (ℓ₁ ⊔ c ⊔ r ⊔ ℓ₂)

  recRep : RepFam o → A o

  data RepFam where
    η : (o : O) → A o → RepFam o
    fix : (o : O) → ⟦ C ⟧ RepFam o → RepFam o
    eq : (x : RepFam o) → η o (recRep x) ≡ x

  recRep (η _ a) = a
  recRep (fix o (s , f)) = α o (s , recRep ∘ f)
  recRep (eq x i) = recRep x

  RepFam↔A : (o : O) → Iso (RepFam o) (A o)
  fun (RepFam↔A o) = recRep
  inv (RepFam↔A o) = η o
  rightInv (RepFam↔A o) p = refl
  leftInv (RepFam↔A o) = eq
  
  data RepΣ : Type (ℓ₁ ⊔ ℓ₂ ⊔ c ⊔ r)

  decodeΣ : RepΣ → Σ[ o ∈ O ] A o
    
  data RepΣ where
    η : (o : O) → A o → RepΣ
    fix : (o : O) → ⟦ C ⟧ (Fiber (fst ∘ decodeΣ)) o → RepΣ
    eq : (x : RepΣ) → η (fst (decodeΣ x)) (snd (decodeΣ x)) ≡ x

  decodeΣ (η o a) = o , a
  decodeΣ (fix o (c , f)) = o , α o (c , λ r → unwrapA _ (f r))
    where
      unwrapA : (o : O) → Fiber (fst ∘ decodeΣ) o → A o
      unwrapA _ (fib a) = snd (decodeΣ a)
  decodeΣ (eq x i) = decodeΣ x

  RepΣ→ΣA : Iso RepΣ (Σ[ o ∈ O ] A o)
  fun      RepΣ→ΣA   = decodeΣ
  inv      RepΣ→ΣA   = uncurry η
  rightInv RepΣ→ΣA p = refl
  leftInv  RepΣ→ΣA   = eq
