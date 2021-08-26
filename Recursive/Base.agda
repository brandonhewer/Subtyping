{-# OPTIONS --cubical --no-import-sorts --safe #-}

module SmallSubtypes.Recursive.Base where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_; I to I′)

open import SmallSubtypes.Container
open import SmallSubtypes.Fiber

private
  variable
    o c c₂ r r₂ ℓ₁ ℓ₂ : Level

module _ {o : Level} {O : Type o} where

  data FreeSTExt (C : Container O O c r) (B : O → Type ℓ₂) : Type (o ⊔ c ⊔ r ⊔ ℓ₂)

  decode : (C : Container O O c r) (B : O → Type ℓ₂) → FreeSTExt C B → O

  data FreeSTExt C B where
    η : (o : O) → B o → FreeSTExt C B
    fix : (o : O) → ⟦ C ⟧ (Fiber (decode C B)) o → FreeSTExt C B
    eq : (x y : FreeSTExt C B) → decode C B x ≡ decode C B y → x ≡ y

  decode C B (η o b) = o
  decode C B (fix o f) = o
  decode C B (eq x y p i) = p i

  module _ {C : Container O O c r} {B : O → Type ℓ₁} where

    elimDecode :
      (P : ∀ {o} → Fiber (decode C B) o → Type ℓ₂) →
      (∀ {o} (x : Fiber (decode C B) o) → isProp (P x)) →
      (∀ o (b : B o) → P (fib (η o b))) →
      ((o : O) (f : ⟦ C ⟧₂ (Fiber (decode C B)) P o) → P (fib (fix o (fst f)))) →
      ∀ {o} (x : Fiber (decode C B) o) → P x
    elimDecode B isPropB f g (fib (η o p)) = f o p
    elimDecode B isPropB f g (fib (fix o h)) =
      g o (h , elimDecode B isPropB f g ∘ snd h)
    elimDecode B isPropB f g (fib (eq x y p i)) =
      isProp→PathP (λ i → isPropB (fib (eq x y p i)))
                   (elimDecode B isPropB f g (fib x))
                   (elimDecode B isPropB f g (fib y)) i

    recFreeSTExt :
      (P : O → Type ℓ₂) → (∀ o → isProp (P o)) →
      (∀ o → B o → P o) →
      ((o : O) → ⟦ C ⟧ P o → P o) →
      (x : FreeSTExt C B) → P (decode C B x)
    recFreeSTExt P isPropP Pp Pr x =
      elimDecode (λ {o} _ → P o) (λ _ → isPropP _) Pp
                 (λ { o ((s , f) , g) → Pr o (s , g) }) (fib x)

    recFreeSTExtΣ :
      (P : O → Type) → (∀ o → isProp (P o)) →
      (∀ o → B o → P o) →
      ((o : O) → ⟦ C ⟧ P o → P o) →
      FreeSTExt C B → Σ[ o ∈ O ] P o
    recFreeSTExtΣ P isPropP Pp Pr x = decode C B x , recFreeSTExt P isPropP Pp Pr x
