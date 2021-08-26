{-# OPTIONS --cubical --no-import-sorts --safe #-}

module SmallSubtypes.Family.Example where

open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.List
open import Cubical.Data.Nat hiding (isEven) renaming (_·_ to _*_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude renaming (ℓ-max to _⊔_; I to I′)

open import SmallSubtypes.Container
open import SmallSubtypes.Family

open Iso

private
  variable
    m n o : ℕ

-- The typical definition of evenness as an inductive family

data isEvenI : ℕ → Type where
  even-zero : isEvenI 0
  even-ss : isEvenI n → isEvenI (suc (suc n))

-- This is a family of propositions

isPropIsEvenI : isProp (isEvenI n)
isPropIsEvenI even-zero   even-zero   = refl
isPropIsEvenI (even-ss p) (even-ss q) = cong even-ss (isPropIsEvenI p q)

{-
  We can easily apply the manual application of our technique to construct
  an alternative representation of isEvenI
-}

data isEven : ℕ → Type where
  even-zero : isEven 0
  even-ss : isEven n → isEven (suc (suc n))
  even-+ : isEven m → isEven n → isEven (m + n)
  trunc/ : isProp (isEven n)

recIsEven : (B : ℕ → Type) → (∀ n → isProp (B n)) →
            B 0 → (∀ n → B n → B (suc (suc n))) →
            (∀ m n → B m → B n → B (m + n)) →
            isEven n → B n
recIsEven B isPropB B0 Bs B+ even-zero = B0
recIsEven B isPropB B0 Bs B+ (even-ss p) = Bs _ (recIsEven B isPropB B0 Bs B+ p)
recIsEven B isPropB B0 Bs B+ (even-+ p q) =
  B+ _ _ (recIsEven B isPropB B0 Bs B+ p) (recIsEven B isPropB B0 Bs B+ q)
recIsEven B isPropB B0 Bs B+ (trunc/ p q i) =
  isPropB _ (recIsEven B isPropB B0 Bs B+ p)
            (recIsEven B isPropB B0 Bs B+ q) i

isEven-pred : isEven (suc (suc n)) → isEven n
isEven-pred = recIsEven B isPropB tt Bs B+
  where
    B : ℕ → Type
    B 0 = ⊤
    B 1 = ⊥
    B (suc (suc n)) = isEven n

    isPropB : ∀ n → isProp (B n)
    isPropB 0 = isPropUnit
    isPropB 1 = isProp⊥
    isPropB (suc (suc n)) = trunc/

    Bs : ∀ n → B n → isEven n
    Bs zero _ = even-zero
    Bs (suc (suc n)) = even-ss

    B+ : ∀ m n → B m → B n → B (m + n)
    B+ zero n x y = y
    B+ (suc (suc m)) n x y = even-+ x (Bs n y)

¬isEven1 : isEven 1 → ⊥
¬isEven1 = recIsEven B isPropB tt (λ _ _ → tt) B+
  where
    B : ℕ → Type
    B 0 = ⊤
    B 1 = ⊥
    B (suc (suc m)) = ⊤

    isPropB : ∀ n → isProp (B n)
    isPropB 0 = isPropUnit
    isPropB 1 = isProp⊥
    isPropB (suc (suc n)) = isPropUnit

    B+ : ∀ m n → B m → B n → B (m + n)
    B+ zero n x y = y
    B+ (suc (suc m)) n x y = tt

{-
  In order to construct a div2 function on isEven, we first define the following
  family of propositions.

  isMultipleOf m n is the type witnessing that n is a multiple of m

  isMultipleOf (suc m) n
  AND
  isMultipleOf m (su c n)

  are always h-props.
-}

isMultipleOf : ℕ → ℕ → Type
isMultipleOf m n = Σ[ k ∈ ℕ ] m * k ≡ n

isPropIsMultipleOf₁ : ∀ m n → isProp (isMultipleOf (suc m) n)
isPropIsMultipleOf₁ m n (k , p) (l , q) =
  Σ≡Prop (λ _ → isSetℕ _ _) (inj-sm· {m} (p ∙ sym q))

isPropIsMultipleOf₂ : ∀ m n → isProp (isMultipleOf m (suc n))
isPropIsMultipleOf₂ zero n (k , p) = absurd (znots p)
isPropIsMultipleOf₂ (suc m) n (k , p) (l , q) =
  Σ≡Prop (λ _ → isSetℕ _ _) (inj-sm· {m} (p ∙ sym q))

isDiv2 : ℕ → Type
isDiv2 = isMultipleOf 2

isDiv2-ss : (n : ℕ) → isDiv2 n → isDiv2 (suc (suc n))
isDiv2-ss _ (m , p) = suc m , cong suc (+-suc m (m + 0) ∙ cong suc p)

¬isDiv2-1 : isDiv2 1 → ⊥
¬isDiv2-1 (zero , p) = znots p
¬isDiv2-1 (suc m , p) = snotz (sym (+-suc m (m + 0)) ∙ cong predℕ p)

isDiv2-pred : (n : ℕ) → isDiv2 (suc (suc n)) → isDiv2 n
isDiv2-pred n (0 , p) = absurd (znots p)
isDiv2-pred n (suc m , p) = m , cong predℕ (sym (+-suc m (m + 0)) ∙ cong predℕ p)

isDiv2-+ : (m n : ℕ) → isDiv2 m → isDiv2 n → isDiv2 (m + n)
isDiv2-+ 0 n p q = q
isDiv2-+ 1 n p = absurd (¬isDiv2-1 p)
isDiv2-+ (suc (suc m)) n p q = isDiv2-ss (m + n) (isDiv2-+ m n (isDiv2-pred m p) q)

isEven→isDiv2 : isEven n → isDiv2 n
isEven→isDiv2 = recIsEven isDiv2 (isPropIsMultipleOf₁ 1) (zero , refl) isDiv2-ss isDiv2-+

div2' : isEven n → ℕ
div2' = fst ∘ isEven→isDiv2

div2 : isEven n → ℕ
div2 {n = 0} p = 0
div2 {n = 1} p = absurd (¬isEven1 p)
div2 {n = suc (suc n)} p = suc (div2 (isEven-pred p))


{-

 Example of lists with related adjacent elements

-}

filter : {A : Type} → (A → Bool) → List A → List A
filter P? [] = []
filter P? (x ∷ xs) with P? x
... | false = filter P? xs
... | true = x ∷ filter P? xs

remove : {A : Type} → ℕ → List A → List A
remove n       []       = []
remove 0       (x ∷ xs) = xs
remove (suc n) (x ∷ xs) = x ∷ remove n xs

module _ {A : Type} (_∼_ : A → A → Type) where

  private
    variable
      x y : A
      xs ys : List A

  data isRelated : List A → Type where
    nil : isRelated []
    sing : (x : A) → isRelated [ x ]
    ind : x ∼ y → isRelated (y ∷ xs) → isRelated (x ∷ y ∷ xs)

  recIsRelated : (B : List A → Type) →
                 B [] → ((x : A) → B [ x ]) →
                 ((x y : A) (xs : List A) → x ∼ y → B (y ∷ xs) → B (x ∷ y ∷ xs)) →
                 isRelated xs → B xs
  recIsRelated B Bn Bs Bi nil = Bn
  recIsRelated B Bn Bs Bi (sing x) = Bs x
  recIsRelated B Bn Bs Bi (ind p q) = Bi _ _ _ p (recIsRelated B Bn Bs Bi q)

  isPropIsRelated : (∀ x y → isProp (x ∼ y)) → isProp (isRelated xs)
  isPropIsRelated isProp∼ nil nil = refl
  isPropIsRelated isProp∼ (sing x) (sing x) = refl
  isPropIsRelated isProp∼ (ind r p) (ind s q) =
    cong₂ ind (isProp∼ _ _ r s) (isPropIsRelated isProp∼ p q)

  data Last∼First : List A → List A → Type where
    nilL : (xs : List A) → Last∼First [] xs
    nilR : (x : A) (xs : List A) → Last∼First (x ∷ xs) []
    sing : (x y : A) (ys : List A) → x ∼ y → Last∼First [ x ] (y ∷ ys)
    ind : (x x' y : A) (xs ys : List A) →
          Last∼First (x' ∷ xs) (y ∷ ys) → Last∼First (x ∷ x' ∷ xs) (y ∷ ys)

  isPropLast∼First : (∀ x y → isProp (x ∼ y)) → isProp (Last∼First xs ys)
  isPropLast∼First isProp∼ (nilL _) (nilL _) = refl
  isPropLast∼First isProp∼ (nilR x xs) (nilR x xs) = refl
  isPropLast∼First isProp∼ (sing x y ys p) (sing x y ys q) =
    cong (sing x y ys) (isProp∼ x y p q)
  isPropLast∼First isProp∼ (ind x x' y xs ys p) (ind x x' y xs ys q) =
    cong (ind x x' y xs ys) (isPropLast∼First isProp∼ p q)

  module _ (trans : ∀ x y z → x ∼ y → y ∼ z → x ∼ z) where

    relRep : x ∼ y → isRelated (y ∷ xs) → isRelated (x ∷ xs)
    relRep p (sing _) = sing _
    relRep p (ind q r) = ind (trans _ _ _ p q) r

    filterRelTrans : (P? : A → Bool) → x ∼ y → isRelated (y ∷ ys) → isRelated (x ∷ filter P? (y ∷ ys))
    filterRelTrans P? p (sing x) with P? x
    ... | false = sing _
    ... | true  = ind p (sing x)
    filterRelTrans P? p (ind {x} {y} q r) with P? x
    ... | false = filterRelTrans P? (trans _ _ _ p q) r
    ... | true  = ind p (filterRelTrans P? q r)

    filterRel : (P? : A → Bool) → isRelated xs → isRelated (filter P? xs)
    filterRel P? nil = nil
    filterRel P? (sing x) with P? x
    ... | false = nil
    ... | true  = sing x
    filterRel P? (ind {x} {y} p q) with P? x
    ... | false = filterRel P? q
    ... | true  = filterRelTrans P? p q

    removeRel : (n : ℕ) → isRelated xs → isRelated (remove n xs)
    removeRel n       nil       = nil
    removeRel zero    (sing x)  = nil
    removeRel (suc n) (sing x)  = sing x
    removeRel zero    (ind x p) = p 
    removeRel 1 (ind {x} {y} p (sing .y)) = sing x
    removeRel (suc (suc n)) (ind {x} {y} p (sing .y)) = ind p (sing y)
    removeRel 1 (ind {x} {y} p (ind q r)) = ind (trans _ _ _ p q) r
    removeRel (suc (suc n)) (ind {x} {y} p (ind q r)) =
      ind p (removeRel (suc n) (ind q r))

  concatRel : isRelated xs → isRelated ys → Last∼First xs ys → isRelated (xs ++ ys)
  concatRel p q (nilL _) = q
  concatRel p q (nilR x xs) = subst (isRelated ∘ (x ∷_)) (sym (++-unit-r xs)) p
  concatRel p q (sing x y ys r) = ind r q
  concatRel (ind s t) q (ind x x' y xs ys r) = ind s (concatRel t q r)

  {-

     Manual application of our technique

  -}

  data isRelatedF : List A → Type where
    nil : isRelatedF []
    sing : (x : A) → isRelatedF [ x ]
    ind : x ∼ y → isRelatedF (y ∷ xs) → isRelatedF (x ∷ y ∷ xs)
    filterF : (P? : A → Bool) → isRelatedF xs → isRelatedF (filter P? xs)
    removeF : (n : ℕ) → isRelatedF xs → isRelatedF (remove n xs)
    concatF : isRelatedF xs → isRelatedF ys → Last∼First xs ys → isRelatedF (xs ++ ys)
    squash : isProp (isRelatedF xs)

  recRelatedF : (B : List A → Type) →
                (∀ xs → isProp (B xs)) →
                B [] → ((x : A) → B [ x ]) →
                (∀ {x y xs} → x ∼ y → B (y ∷ xs) → B (x ∷ y ∷ xs)) →
                (∀ {xs} (P? : A → Bool) → B xs → B (filter P? xs)) →
                (∀ {xs} (n : ℕ) → B xs → B (remove n xs)) →
                (∀ {xs ys} → B xs → B ys → Last∼First xs ys → B (xs ++ ys)) →
                isRelatedF xs → B xs
  recRelatedF B isPropB Bn Bs Bi Bf Br Bc nil = Bn
  recRelatedF B isPropB Bn Bs Bi Bf Br Bc (sing x) = Bs x
  recRelatedF B isPropB Bn Bs Bi Bf Br Bc (ind p q) =
    Bi p (recRelatedF B isPropB Bn Bs Bi Bf Br Bc q)
  recRelatedF B isPropB Bn Bs Bi Bf Br Bc (filterF P? p) =
    Bf P? (recRelatedF B isPropB Bn Bs Bi Bf Br Bc p)
  recRelatedF B isPropB Bn Bs Bi Bf Br Bc (removeF n p) =
    Br n (recRelatedF B isPropB Bn Bs Bi Bf Br Bc p)
  recRelatedF B isPropB Bn Bs Bi Bf Br Bc (concatF p q r) =
    Bc (recRelatedF B isPropB Bn Bs Bi Bf Br Bc p)
       (recRelatedF B isPropB Bn Bs Bi Bf Br Bc q) r
  recRelatedF B isPropB Bn Bs Bi Bf Br Bc (squash p q i) =
    isPropB _ (recRelatedF B isPropB Bn Bs Bi Bf Br Bc p)
              (recRelatedF B isPropB Bn Bs Bi Bf Br Bc q) i

  isRelated→F : isRelated xs → isRelatedF xs
  isRelated→F nil       = nil
  isRelated→F (sing x)  = sing x
  isRelated→F (ind p q) = ind p (isRelated→F q)

  module _ (isProp∼ : (x y : A) → isProp (x ∼ y))
           (trans : ∀ x y z → x ∼ y → y ∼ z → x ∼ z) where

    F→isRelated : isRelatedF xs → isRelated xs
    F→isRelated =
      recRelatedF isRelated (λ _ → isPropIsRelated isProp∼)
                  nil sing ind (filterRel trans) (removeRel trans) concatRel

    isRelated↔F : Iso (isRelated xs) (isRelatedF xs)
    fun      isRelated↔F   = isRelated→F
    inv      isRelated↔F   = F→isRelated
    rightInv isRelated↔F p = squash _ p
    leftInv  isRelated↔F p = isPropIsRelated isProp∼ _ p

{-
  The original definition of the less than relation on natural numbers
-}

data _<'_ : ℕ → ℕ → Type where
  z<s : 0 <' suc n
  s<s : m <' n → suc m <' suc n

{-
  Result of manually applying our encoding
-}

data _<_ : ℕ → ℕ → Type where
  z<s : 0 < suc n
  s<s : m < n → suc m < suc n
  n<sn : n < suc n
  trans< : m < n → n < o → m < o
  trunc/ : isProp (m < n)

rec< : (B : ℕ → ℕ → Type) →
       (∀ m n → isProp (B m n)) →
       (∀ n → B 0 (suc n)) →
       (∀ m n → B m n → B (suc m) (suc n)) →
       (∀ n → B n (suc n)) →
       (∀ m n o → B m n → B n o → B m o) →
       m < n → B m n
rec< B isPropB Bzs Bss Bnsn Btr z<s = Bzs _
rec< B isPropB Bzs Bss Bnsn Btr (s<s p) =
  Bss _ _ (rec< B isPropB Bzs Bss Bnsn Btr p)
rec< B isPropB Bzs Bss Bnsn Btr n<sn = Bnsn _
rec< B isPropB Bzs Bss Bnsn Btr (trans< p q) =
  Btr _ _ _ (rec< B isPropB Bzs Bss Bnsn Btr p)
            (rec< B isPropB Bzs Bss Bnsn Btr q)
rec< B isPropB Bzs Bss Bnsn Btr (trunc/ p q i) =
  isPropB _ _ (rec< B isPropB Bzs Bss Bnsn Btr p)
              (rec< B isPropB Bzs Bss Bnsn Btr q) i

¬m<0 : m < 0 → ⊥
¬m<0 (trans< p q) = ¬m<0 q
¬m<0 (trunc/ p q i) = isProp⊥ (¬m<0 p) (¬m<0 q) i

p<p : suc m < suc n → m < n
p<p (s<s p) = p
p<p n<sn = n<sn
p<p (trans< {n = zero} p q) = absurd (¬m<0 p)
p<p (trans< {n = suc n} p q) = trans< (p<p p) (p<p q)
p<p (trunc/ p q i) = trunc/ (p<p p) (p<p q) i
