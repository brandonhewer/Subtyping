{-# OPTIONS --cubical --no-import-sorts --safe #-}

module SmallSubtypes.Family.Base where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_; I to I′)

open import SmallSubtypes.Container

private
  variable
    o c r c₂ r₂ ℓ₁ ℓ₂ : Level
    O : Type o
    C : Container O O c r
    D : Container O O c₂ r₂
    B : O → Type ℓ₁

{-
  Monads on families of propositions

  This is in fact the entire definition, as the monadic laws are
  trivially satisified by virtue of isPropM.
-}

record PropMonad {O : Type o}
                 (C : (O → Type ℓ₁) → O → Type ℓ₂)
                 : Type (o ⊔ ℓ-suc ℓ₁ ⊔ ℓ₂) where
  field
    isPropM : (B : O → Type ℓ₁) → ∀ o → isProp (C B o)
    return : (B : O → Type ℓ₁) → ∀ o → B o → C B o
    bind   : (B₁ B₂ : O → Type ℓ₁) →
             ∀ {o} → C B₁ o → (∀ {o} → B₁ o → C B₂ o) → C B₂ o

{-
  The 'free' extended propositional family on an indexed container C.

  The family FreePF C P is equal to P (up to a path) if there is a C-algebra
  for which P is the carrier, i.e. there is a term

     α : ∀ o → ⟦ C ⟧ P o → P o

  See Properties.agda for this isomorphism.
-}

data FreePM {O : Type o} (C : Container O O c r)
            (P : O → Type ℓ₁) : O → Type (o ⊔ c ⊔ r ⊔ ℓ₁) where
  η : (o : O) → P o → FreePM C P o
  fix : (o : O) → ⟦ C ⟧ (FreePM C P) o → FreePM C P o
  squash : (o : O) → isProp (FreePM C P o)

recFreePM : (P : O → Type ℓ₂) →
            (∀ o → isProp (P o)) →
            (∀ o → B o → P o) →
            (∀ o → ⟦ C ⟧ P o → P o) →
            ∀ {o} → FreePM C B o → P o
recFreePM P isPropP ηP αP (η _ x)          = ηP _ x
recFreePM P isPropP ηP αP (fix _ (s , f))  = αP _ (s , recFreePM P isPropP ηP αP ∘ f)
recFreePM P isPropP ηP αP (squash o x y i) =
  isPropP _ (recFreePM P isPropP ηP αP x)
            (recFreePM P isPropP ηP αP y) i
            
elimFreePF : (P : ∀ {o} → FreePM C B o → Type ℓ₂) →
             (∀ {o} (x : FreePM C B o) → isProp (P x)) →
             (∀ {o} (p : B o) → P (η o p)) →
             (∀ {o} (f : ⟦ C ⟧₂ (FreePM C B) P o) → P (fix o (fst f))) →
             ∀ {o} (x : FreePM C B o) → P x
elimFreePF P isPropP ηP αP (η _ x) = ηP x
elimFreePF P isPropP ηP αP (fix _ f) =
  αP (f , λ r → elimFreePF P isPropP ηP αP (snd f r))
elimFreePF P isPropP ηP αP (squash o x y i) =
  isProp→PathP (λ i → isPropP (squash o x y i))
               (elimFreePF P isPropP ηP αP x)
               (elimFreePF P isPropP ηP αP y) i

-- Lift maps between families to maps between propositional families

mapPF : (B₂ : O → Type ℓ₂) → (∀ o → B o → B₂ o) →
        ∀ {o} → FreePM C B o → FreePM C B₂ o
mapPF B₂ f =
  recFreePM (λ o → FreePM _ B₂ o) squash
            (λ o → η o ∘ f o) fix

-- Monad composition map

joinPF : ∀ {o} → FreePM C (FreePM C B) o → FreePM C B o
joinPF = recFreePM (FreePM _ _) squash (λ _ x → x) fix

{-
  Bind is written in this form to be compatible with Agda's do notation
-}

_>>=_ : {B₂ : O → Type ℓ₂} → ∀ {o} → FreePM C B o →
        (((o , _) : Σ[ o ∈ O ] B o) → FreePM C B₂ o) → FreePM C B₂ o
x >>= f = joinPF (mapPF _ (curry f) x)

-- FreePF C is a RawPMonad

open PropMonad

FreePMonad : (C : Container O O c r) → PropMonad {ℓ₁ = ℓ₁} (FreePM C)
isPropM (FreePMonad C) _ = squash
return (FreePMonad C) _ = η
bind (FreePMonad C) _ _ x f =
  recFreePM (FreePM C _) squash
            (λ _ → f) fix x

-- Hoist an indexed container morphism to a morphism between free propositional families.

{-
hoist : {C₁ : Container O O c r} {C₂ : Container O O c₂ r₂} →
        (f : C₁ ⇒ C₂) {B : O → Type ℓ₁} →
        ∀ {o} → FreePM C₁ B o → FreePM C₂ B o
hoist f {B = B} =
  recFreePM (λ o → FreePM _ _ o) squash
            (λ o x → η _ x)
            (λ o → fix o ∘ ⟪ f ⟫ (FreePM _ _))
            -}

hoist : (f : C ⇒ D) → ∀ {o} → FreePM C B o → FreePM D B o
hoist f =
  recFreePM (λ o → FreePM _ _ o) squash
            (λ o x → η _ x)
            (λ o → fix o ∘ ⟪ f ⟫ (FreePM _ _))

-- Lift a map of indexed containers to a homomorphism between free propositional monad families

foldFreePM : {c₂ r₂ : Level} {D : Container O O c₂ r₂}
             {B : O → Type (c₂ ⊔ r₂ ⊔ ℓ₂)} → PropMonad ⟦ D ⟧ → C ⇒ D → ∀ {o} → FreePM C B o → ⟦ D ⟧ B o
foldFreePM {D = D} {B = B} MD f =
  recFreePM (⟦ D ⟧ B) (isPropM MD B) (return MD B)
            λ o g → bind MD (⟦_⟧ D B) B (⟪ f ⟫ (⟦ D ⟧ B) g) (λ x → x)

-- The unit of the adjunction between indexed containers and RawPMonad's

unitPM : {B : O → Type ℓ₁} → ∀ {o} → ⟦ C ⟧ B o → FreePM C B o
unitPM (s , f) = fix _ (s , η _ ∘ f)
