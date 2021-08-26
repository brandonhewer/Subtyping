{-# OPTIONS --cubical --no-import-sorts --safe #-}

module SmallSubtypes.Fiber where

open import Cubical.Data.Sigma hiding (I)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_; I to I′)

open import Cubical.Functions.Embedding

private
  doubleCompRefl : ∀ {ℓ₁} {A : Type ℓ₁} {x y : A} (p : x ≡ y) → p ∙∙ refl ∙∙ refl ≡ p
  doubleCompRefl p = sym (leftright p refl) ∙ sym (leftright refl p) ∙ sym (lUnit p)

module _ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} where

  private
    variable
      f : A → B
      b : B

  data Fiber (f : A → B) : B → Type (ℓ₁ ⊔ ℓ₂) where
    fib : (a : A) → Fiber f (f a)

  unwrap : Fiber f b → A
  unwrap (fib a) = a

  unwrap-β : (x : Fiber f b) → f (unwrap x) ≡ b
  unwrap-β (fib a) = refl

  subst-unwrap : (x : Fiber f b) → subst (Fiber f) (unwrap-β x) (fib (unwrap x)) ≡ x
  subst-unwrap {f = f} (fib a) = substRefl {B = Fiber f} (fib a)

  isEmbedding→hasPropFibers' :
    isEmbedding f → ∀ b → isProp (Fiber f b)
  isEmbedding→hasPropFibers' {f = f} isEmbedf _ (fib a) b =
    let ((p , q) , r) = equiv-proof (isEmbedf (unwrap b) a) (unwrap-β b)
     in sym (
          subst (λ p → subst (Fiber f) p (fib (unwrap b)) ≡ fib a) q
                (fromPathP (cong fib p))
        ) ∙ subst-unwrap b

  isEmbedding-cong : isEmbedding f → ∀ x y → isEmbedding (cong {x = x} {y = y} f)
  isEmbedding-cong isEmbedf x y = isEquiv→isEmbedding (isEmbedf x y)

isInjective-cong :
  ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} →
  (∀ a → isProp (B a)) → {x y : Σ A B} →
  (p q : x ≡ y) → cong fst p ≡ cong fst q → p ≡ q
isInjective-cong isPropB p q e =
  fst (fst (equiv-proof (isEmbedding-cong (λ _ _ → isEmbeddingFstΣProp isPropB) _ _ p q) e))

hasPropFibers-ΣProp :
  ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : B → Type ℓ₃} →
    (∀ b → isProp (C b)) → (f : A → Σ[ b ∈ B ] C b) →
    hasPropFibers (fst ∘ f) → hasPropFibers f
hasPropFibers-ΣProp isPropC f isEmbedff (b , c) (a₁ , p) =
  J (λ bc p → (y : fiber f bc) → (a₁ , p) ≡ y)
    (λ { (a₂ , q) →
           let r = isEmbedff (fst (f a₁)) (a₁ , refl) (a₂ , cong fst q)
            in ΣPathP (cong fst r ,
                       transport (sym (PathP≡doubleCompPathˡ _ _ _ _))
                                 (doubleCompRefl (sym (cong (f ∘ fst) r)) ∙
                                  isInjective-cong isPropC (sym (cong (f ∘ fst) r)) q
                                    (sym (doubleCompRefl (sym (cong (fst ∘ f ∘ fst) r))) ∙
                                     transport (PathP≡doubleCompPathˡ _ _ _ _) (cong snd r))))
       }) p
