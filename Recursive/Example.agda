{-# OPTIONS --cubical --no-import-sorts --safe #-}

module SmallSubtypes.Recursive.Example where

open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.List
open import Cubical.Data.Nat hiding (isEven) renaming (_·_ to _*_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_; I to I′)

open import SmallSubtypes.Container
open import SmallSubtypes.Fiber
open import SmallSubtypes.Recursive
open import SmallSubtypes.Family.Example

private
  variable
    m n o : ℕ

module _ {A : Type} (_∼_ : A → A → Type) where

  data RelList : Type

  toList : RelList → List A

  data RelList where
    η : (xs : List A) → isRelated _∼_ xs → RelList
    filterR : (A → Bool) → RelList → RelList
    removeR : ℕ → RelList → RelList
    concatR : RelList → RelList → RelList
    un : (x y : RelList) → toList x ≡ toList y → x ≡ y

  toList (η xs p) = xs
  toList (filterR P? xs) = filter P? (toList xs)
  toList (removeR n xs) = remove n (toList xs)
  toList (concatR xs ys) = toList xs ++ toList ys
  toList (un xs ys p i) = p i

  hasPropFibersToList : (xs : List A) → isProp (Fiber toList xs)
  hasPropFibersToList .(toList a) (fib a) y =
    sym (fromPathP (cong fib (un (unwrap y) a (unwrap-β y)))) ∙
    subst-unwrap y
