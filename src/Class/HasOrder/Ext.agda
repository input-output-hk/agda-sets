{-# OPTIONS --safe --no-import-sorts #-}

-- Extensions to Class.HasOrder: conversions between HasDecTotalOrder≡
-- and DecTotalOrder, a Maybe ordering, and closure of HDTO≡ under
-- common type constructors (×, Maybe, List).

module Class.HasOrder.Ext where

open import abstract-set-theory.Prelude

open import Class.HasOrder
  using (HasDecTotalOrder; HasTotalOrder; HasPartialOrder; HasPreorder;
         HasDecTotalOrder≡)
open import Class.HasOrder.Core
  using (hasPreorderFromNonStrict; hasPartialOrderFromNonStrict)

open import Relation.Binary
  using (Antisymmetric; IsDecTotalOrder; IsPreorder; IsTotalOrder; IsPartialOrder;
         IsEquivalence)
  renaming (Decidable to Dec₂)
open import Relation.Binary.Bundles using (DecTotalOrder)

private variable
  A B : Type

------------------------------------------------------------------------
-- Conversions between HDTO≡ and DecTotalOrder
------------------------------------------------------------------------

HDTO≡ : Type → Type₁
HDTO≡ A = HasDecTotalOrder≡ {A = A} {zeroˡ} {zeroˡ}

-- Convert HasDecTotalOrder≡ to a DecTotalOrder bundle.
-- Derives DecEq from antisymmetry + decidable ≤.
toDecTotalOrder : HDTO≡ A → DecTotalOrder 0ℓ 0ℓ 0ℓ
toDecTotalOrder {A} hdto = record
  { Carrier         = A
  ; _≈_             = _≡_
  ; _≤_             = HasPreorder._≤_ hp
  ; isDecTotalOrder = record
    { isTotalOrder = HasTotalOrder.≤-isTotalOrder ht
    ; _≟_          = _≟ᵒ_
    ; _≤?_         = _≤ᵒ?_
    }
  }
  where
    ht  = HasDecTotalOrder.hasTotalOrder hdto
    hpo = HasTotalOrder.hasPartialOrder ht
    hp  = HasPartialOrder.hasPreorder hpo
    _≤ᵒ?_ : Dec₂ (HasPreorder._≤_ hp)
    _≤ᵒ?_ = dec² ⦃ HasDecTotalOrder.dec-≤ hdto ⦄

    _≟ᵒ_ : Dec₂ (_≡_ {A = A})
    _≟ᵒ_ x y with x ≤ᵒ? y | y ≤ᵒ? x
    ... | yes x≤y | yes y≤x = yes (HasPartialOrder.≤-antisym hpo x≤y y≤x)
    ... | yes _   | no  y≰x = no (λ where refl → y≰x (HasPreorder.≤-refl hp))
    ... | no  x≰y | _       = no (λ where refl → x≰y (HasPreorder.≤-refl hp))

-- Convert a DecTotalOrder back to HDTO≡,
-- given a proof that the bundle's _≈_ implies propositional equality.
fromDecTotalOrder : (dto : DecTotalOrder 0ℓ 0ℓ 0ℓ) →
  (∀ {x y} → DecTotalOrder._≈_ dto x y → x ≡ y) →
  HDTO≡ (DecTotalOrder.Carrier dto)
fromDecTotalOrder dto ≈⇒≡ = record
  { hasTotalOrder = record
    { hasPartialOrder = hpo
    ; ≤-total = IsTotalOrder.total (IsDecTotalOrder.isTotalOrder idto)
    }
  ; dec-≤ = ⁇² IsDecTotalOrder._≤?_ idto
  ; dec-< = ⁇² dec-<′
  }
  where
    open DecTotalOrder dto using (Carrier; _≈_) renaming (_≤_ to _≤d_)
    idto = DecTotalOrder.isDecTotalOrder dto
    ipo = IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder idto)
    ipre = IsPartialOrder.isPreorder ipo

    ≡-isPreorder : IsPreorder _≡_ _≤d_
    ≡-isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive     = λ where refl → IsPreorder.refl ipre
      ; trans         = IsPreorder.trans ipre
      }

    _≟d_ : Dec₂ (_≡_ {A = Carrier})
    _≟d_ x y with IsDecTotalOrder._≟_ idto x y
    ... | yes x≈y = yes (≈⇒≡ x≈y)
    ... | no  x≉y = no (λ where refl → x≉y (IsEquivalence.refl (IsPreorder.isEquivalence ipre)))

    hp : HasPreorder
    hp = hasPreorderFromNonStrict ≡-isPreorder _≟d_

    antisym-≡ : Antisymmetric _≡_ _≤d_
    antisym-≡ x≤y y≤x = ≈⇒≡ (IsPartialOrder.antisym ipo x≤y y≤x)

    hpo : HasPartialOrder
    hpo = hasPartialOrderFromNonStrict ≡-isPreorder _≟d_ antisym-≡

    open import Relation.Binary.Construct.NonStrictToStrict _≡_ _≤d_ as SNS

    dec-<′ : Dec₂ SNS._<_
    dec-<′ x y with IsDecTotalOrder._≤?_ idto x y | _≟d_ x y
    ... | yes x≤y | yes x≡y = no (λ (x≤y' , x≢y) → x≢y x≡y)
    ... | yes x≤y | no  x≢y = yes (x≤y , x≢y)
    ... | no  x≰y | _       = no (λ (x≤y , _) → x≰y x≤y)

------------------------------------------------------------------------
-- DecTotalOrder on Maybe: nothing ≤ everything, just x ≤ just y ↔ x ≤ y
------------------------------------------------------------------------

module MaybeOrder where

  data _≤ᴹ_ {A : Type} (R : A → A → Type) : Maybe A → Maybe A → Type where
    nothing≤   : ∀ {x} → _≤ᴹ_ R nothing x
    just≤just  : ∀ {x y} → R x y → _≤ᴹ_ R (just x) (just y)

  module _ {A : Type} {_≤d_ : A → A → Type}
           (≤-refl′ : ∀ {x} → x ≤d x)
           (≤-trans′ : ∀ {x y z} → x ≤d y → y ≤d z → x ≤d z) where

    ≤ᴹ-refl : ∀ {x} → _≤ᴹ_ _≤d_ x x
    ≤ᴹ-refl {nothing} = nothing≤
    ≤ᴹ-refl {just _}  = just≤just ≤-refl′

    ≤ᴹ-trans : ∀ {x y z} → _≤ᴹ_ _≤d_ x y → _≤ᴹ_ _≤d_ y z → _≤ᴹ_ _≤d_ x z
    ≤ᴹ-trans nothing≤       _               = nothing≤
    ≤ᴹ-trans (just≤just p)  (just≤just q)   = just≤just (≤-trans′ p q)

  module _ {A : Type} {_≤d_ : A → A → Type}
           (≤-antisym′ : ∀ {x y} → x ≤d y → y ≤d x → x ≡ y) where

    ≤ᴹ-antisym : ∀ {x y} → _≤ᴹ_ _≤d_ x y → _≤ᴹ_ _≤d_ y x → x ≡ y
    ≤ᴹ-antisym nothing≤       nothing≤       = refl
    ≤ᴹ-antisym (just≤just p)  (just≤just q)  = cong just (≤-antisym′ p q)

  module _ {A : Type} {_≤d_ : A → A → Type}
           (≤-total′ : ∀ x y → x ≤d y ⊎ y ≤d x) where

    ≤ᴹ-total : ∀ x y → _≤ᴹ_ _≤d_ x y ⊎ _≤ᴹ_ _≤d_ y x
    ≤ᴹ-total nothing  _        = inj₁ nothing≤
    ≤ᴹ-total _        nothing  = inj₂ nothing≤
    ≤ᴹ-total (just x) (just y) with ≤-total′ x y
    ... | inj₁ x≤y = inj₁ (just≤just x≤y)
    ... | inj₂ y≤x = inj₂ (just≤just y≤x)

  module _ {A : Type} {_≤d_ : A → A → Type}
           (≤-dec′ : ∀ x y → Dec (x ≤d y)) where

    ≤ᴹ-dec : ∀ x y → Dec (_≤ᴹ_ _≤d_ x y)
    ≤ᴹ-dec nothing  _        = yes nothing≤
    ≤ᴹ-dec (just x) nothing  = no (λ ())
    ≤ᴹ-dec (just x) (just y) with ≤-dec′ x y
    ... | yes x≤y = yes (just≤just x≤y)
    ... | no  x≰y = no  (λ where (just≤just p) → x≰y p)

Maybe-decTotalOrder : (dto : DecTotalOrder 0ℓ 0ℓ 0ℓ)
  → DecTotalOrder.Carrier dto ≡ A
  → (∀ {x y} → DecTotalOrder._≈_ dto x y → x ≡ y)
  → DecTotalOrder 0ℓ 0ℓ 0ℓ
Maybe-decTotalOrder {A} dto refl ≈⇒≡ = record
  { Carrier = Maybe A
  ; _≈_ = _≡_
  ; _≤_ = _≤ᴹ_ _≤d_
  ; isDecTotalOrder = record
    { isTotalOrder = record
      { isPartialOrder = record
        { isPreorder = record
          { isEquivalence = isEquivalence
          ; reflexive     = λ where refl → ≤ᴹ-refl ≤-refl ≤-trans
          ; trans         = ≤ᴹ-trans ≤-refl ≤-trans
          }
        ; antisym = ≤ᴹ-antisym (λ p q → ≈⇒≡ (antisym p q))
        }
      ; total = ≤ᴹ-total total
      }
    ; _≟_  = ≟ᴹ
    ; _≤?_ = ≤ᴹ-dec _≤?d_
    }
  }
  where
    open MaybeOrder
    open DecTotalOrder dto using () renaming (_≤_ to _≤d_; _≤?_ to _≤?d_)
    open DecTotalOrder dto using (isDecTotalOrder)
    open IsDecTotalOrder isDecTotalOrder using (total) renaming (_≟_ to _≟d'_)
    open IsDecTotalOrder isDecTotalOrder
      using () renaming (isPartialOrder to ipo)
    open IsPartialOrder ipo using (antisym)
    open IsPreorder (IsPartialOrder.isPreorder ipo)
      using () renaming (refl to ≤-refl; trans to ≤-trans)

    ≈-refl′ : ∀ {x : A} → DecTotalOrder._≈_ dto x x
    ≈-refl′ = IsEquivalence.refl (IsPreorder.isEquivalence (IsPartialOrder.isPreorder ipo))

    ≟d : (x y : A) → Dec (x ≡ y)
    ≟d x y with _≟d'_ x y
    ... | yes p = yes (≈⇒≡ p)
    ... | no ¬p = no λ where refl → ¬p ≈-refl′

    ≟ᴹ : Dec₂ (_≡_ {A = Maybe A})
    ≟ᴹ nothing  nothing  = yes refl
    ≟ᴹ nothing  (just _) = no (λ ())
    ≟ᴹ (just _) nothing  = no (λ ())
    ≟ᴹ (just x) (just y) with ≟d x y
    ... | yes refl = yes refl
    ... | no  x≢y = no (λ where refl → x≢y refl)

------------------------------------------------------------------------
-- HDTO≡ closures for common type constructors
------------------------------------------------------------------------

open import Data.Product.Relation.Binary.Lex.NonStrict
  using (×-decTotalOrder)
open import Data.List.Relation.Binary.Lex.NonStrict
  using (≤-decTotalOrder)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using (≡×≡⇒≡)
open import Data.List.Relation.Binary.Pointwise
  using (Pointwise-≡⇒≡)

HDTO≡-× : HDTO≡ A → HDTO≡ B → HDTO≡ (A × B)
HDTO≡-× ha hb = fromDecTotalOrder
  (×-decTotalOrder (toDecTotalOrder ha) (toDecTotalOrder hb))
  ≡×≡⇒≡

HDTO≡-Maybe : HDTO≡ A → HDTO≡ (Maybe A)
HDTO≡-Maybe ha = fromDecTotalOrder
  (Maybe-decTotalOrder (toDecTotalOrder ha) refl id)
  id

HDTO≡-List : HDTO≡ A → HDTO≡ (List A)
HDTO≡-List ha = fromDecTotalOrder
  (≤-decTotalOrder (toDecTotalOrder ha))
  Pointwise-≡⇒≡
