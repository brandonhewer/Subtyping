{-# OPTIONS --cubical --no-import-sorts --safe #-}

module SmallSubtypes.Recursive.Properties where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_)

open import Cubical.Functions.Embedding

open import SmallSubtypes.Container
open import SmallSubtypes.Family
open import SmallSubtypes.Fiber
open import SmallSubtypes.Recursive.Base

private
  variable
    c r c₂ r₂ ℓ₁ : Level

open Iso

module _ {o : Level} {O : Type o} where

  module _ {C : Container O O c r} {B : O → Type ℓ₁} where

    module _ (x : FreeSTExt C B) where

      eqSideFaces : (i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) (FreeSTExt C B)
      eqSideFaces i j k (i = i0) = eq x x refl j
      eqSideFaces i j k (i = i1) = eq x x refl (j ∨ k)
      eqSideFaces i j k (j = i0) = eq x x refl (~ i ∨ k)
      eqSideFaces i j k (j = i1) = x

      eqBase : PathP (λ i → eq x x refl (~ i) ≡ x) (eq x x refl) (eq x x refl)
      eqBase i = eq (eq x x refl (~ i)) x refl

      eqRefl : eq x x refl ≡ refl
      eqRefl i j = hcomp (eqSideFaces i j) (eqBase i j)

    eqCong : {x y : FreeSTExt C B} (p : x ≡ y) → eq x y (cong (decode C B) p) ≡ p
    eqCong = J (λ y p → eq _ y (cong (decode C B) p) ≡ p) (eqRefl _)

    decodePathIso : (x y : FreeSTExt C B) → Iso (x ≡ y) (decode C B x ≡ decode C B y)
    fun      (decodePathIso x y)   = cong (decode C B)
    inv      (decodePathIso x y)   = eq x y
    rightInv (decodePathIso x y) p = refl
    leftInv  (decodePathIso x y)   = eqCong

  isEmbeddingDecode : (C : Container O O c r) (B : O → Type ℓ₁) → isEmbedding (decode C B)
  isEmbeddingDecode C B x y = isoToIsEquiv (decodePathIso x y)

  {-

    We can alternatively prove that decode has propositional fibers as below.

  -}

  hasPropFibersDecode : (C : Container O O c r) (B : O → Type ℓ₁) →
                        ∀ o → isProp (Fiber (decode C B) o)
  hasPropFibersDecode C B .(decode C B a) (fib a) y =
    sym (fromPathP (cong fib (eq (unwrap y) a (unwrap-β y)))) ∙ subst-unwrap y

  module _ {C : Container O O c r} {B : O → Type ℓ₁} where

    mapDecode : {D : Container O O c₂ r₂} →
                (C ⇒ D) → ∀ {o} → Fiber (decode C B) o → Fiber (decode D B) o
    mapDecode {D = D} f (fib a) =
      recFreeSTExt (Fiber (decode D B)) (hasPropFibersDecode D B)
                   (λ o b → fib (η o b))
                   (λ o h → fib (fix o (⟪ f ⟫ (Fiber (decode D B)) h))) a

    mapFreeSTExt : {D : Container O O c₂ r₂} →
                   (C ⇒ D) → FreeSTExt C B → FreeSTExt D B
    mapFreeSTExt f = unwrap ∘ mapDecode f ∘ fib

    FreePM→Decode : ∀ {o} → FreePM C B o → Fiber (decode C B) o
    FreePM→Decode =
      recFreePM (Fiber (decode C B)) (hasPropFibersDecode C B)
                (λ o b → fib (η o b)) (λ o f → fib (fix o f))

    Decode→FreePM : ∀ {o} → Fiber (decode C B) o → FreePM C B o
    Decode→FreePM (fib a) = recFreeSTExt (FreePM C B) squash η fix a
  
    FreePM↔Decode : ∀ o → Iso (FreePM C B o) (Fiber (decode C B) o)
    fun      (FreePM↔Decode o)   = FreePM→Decode
    inv      (FreePM↔Decode o)   = Decode→FreePM
    rightInv (FreePM↔Decode o) p = hasPropFibersDecode C B o _ p
    leftInv  (FreePM↔Decode o) p = squash o _ p

    PM→STExt : ∀ {o} (x : FreePM C B o) → FreeSTExt C B
    PM→STExt x with FreePM→Decode x
    ... | (fib a) = a

    STExt→PM : (x : FreeSTExt C B) → FreePM C B (decode C B x)
    STExt→PM = recFreeSTExt (FreePM C B) squash η fix

    STExt→ΣPM : FreeSTExt C B → Σ[ o ∈ O ] FreePM C B o
    STExt→ΣPM x = decode C B x , STExt→PM x

    STExt→ΣPM→STExt : (x : FreeSTExt C B) → PM→STExt (STExt→PM x) ≡ x
    STExt→ΣPM→STExt x = eq _ _ (lem (STExt→PM x))
      where
        lem : ∀ {o} (x : FreePM C B o) → decode C B (PM→STExt x) ≡ o
        lem x with FreePM→Decode x
        ... | fib a = refl

    ΣPM→STExt→ΣPM : ∀ {o} (x : FreePM C B o) → STExt→ΣPM (PM→STExt x) ≡ (o , x)
    ΣPM→STExt→ΣPM x with FreePM→Decode x
    ... | (fib a) = Σ≡Prop squash refl

    ΣPM↔STExt : Iso (Σ[ o ∈ O ] FreePM C B o) (FreeSTExt C B)
    fun      ΣPM↔STExt = PM→STExt ∘ snd
    inv      ΣPM↔STExt = STExt→ΣPM
    rightInv ΣPM↔STExt = STExt→ΣPM→STExt
    leftInv  ΣPM↔STExt (o , x) = ΣPM→STExt→ΣPM x
