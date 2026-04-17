{-# OPTIONS --safe --no-import-sorts #-}

module Axiom.Set.SortedList where

open import abstract-set-theory.Prelude

open import Axiom.Set
open import Class.HasOrder.Ext

import Function.Related.Propositional as R
import Relation.Nullary.Decidable as Dec

open import Data.List as L
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ˡ_; find to ∈-find)
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Binary.Lex.NonStrict
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open import Data.List.Relation.Binary.Pointwise using (Pointwise-≡⇒≡; ≡⇒Pointwise-≡)
open import Data.List.Relation.Unary.Sorted.TotalOrder.Properties
open import Data.Product
open import Relation.Binary.Bundles
import Data.List.Sort
import Data.List.Relation.Unary.Sorted.TotalOrder

module SortedOps {A : Type} (ha : HDTO≡ A) where
  private
    O  = toDecTotalOrder ha
    TO = DecTotalOrder.totalOrder O
  open Data.List.Sort O using (sort; sort-↭; sort-↗)
  open Data.List.Relation.Unary.Sorted.TotalOrder TO using (Sorted)

  record SortedList : Type where
    constructor mkSL
    field
      list : List A
      .sorted : Sorted list
  open SortedList public

  _∈ˢ_ : A → SortedList → Type
  a ∈ˢ sl = a ∈ˡ list sl

  mkSorted : List A → SortedList
  mkSorted l = mkSL (sort l) (sort-↗ l)

  ∈-mkSorted⇔ : ∀ {a l} → a ∈ˡ l ⇔ a ∈ˢ mkSorted l
  ∈-mkSorted⇔ {l = l} = mk⇔ (Any-resp-↭ (↭-sym (sort-↭ l))) (Any-resp-↭ (sort-↭ l))

  filterˢ : ∀ {P : A → Type} → Decidable¹ P → SortedList → SortedList
  filterˢ P? (mkSL l s) = mkSL (filter P? l) (filter⁺ TO P? s)

------------------------------------------------------------------------
-- The SortedList Model
------------------------------------------------------------------------

sorted-sc : SetConstraint {zeroˡ} {sucˡ zeroˡ}
sorted-sc = record
  { constraint = HDTO≡
  ; c-×       = λ ca cb → mkCstr (HDTO≡-× (getCstr ca) (getCstr cb))
  ; c-Maybe   = λ ca → mkCstr (HDTO≡-Maybe (getCstr ca))
  }

SL-≡ : ∀ {A} (ha : HDTO≡ A) {sl₁ sl₂ : SortedOps.SortedList ha}
  → SortedOps.list sl₁ ≡ SortedOps.list sl₂ → sl₁ ≡ sl₂
SL-≡ _ refl = refl

module Helpers {A : Type} ⦃ ha : HDTO≡ A ⦄ where

  module Inner = SortedOps ha

  c-SortedList : HDTO≡ (SortedOps.SortedList ha)
  c-SortedList = fromDecTotalOrder SL-dto id
    where
      module DTO = DecTotalOrder (≤-decTotalOrder (toDecTotalOrder ha))
      open Inner using (SortedList; list)

      SL-dto : DecTotalOrder 0ℓ 0ℓ 0ℓ
      SL-dto = record
        { Carrier = SortedList
        ; _≈_ = _≡_
        ; _≤_ = DTO._≤_ on list
        ; isDecTotalOrder = record
          { isTotalOrder = record
            { isPartialOrder = record
              { isPreorder = record
                { isEquivalence = isEquivalence
                ; reflexive = λ where refl → DTO.refl
                ; trans     = DTO.trans
                }
              ; antisym = λ p q → SL-≡ ha (Pointwise-≡⇒≡ (DTO.antisym p q))
              }
            ; total = λ sl₁ sl₂ → DTO.total (list sl₁) (list sl₂)
            }
          ; _≟_ = λ sl₁ sl₂ → Dec.map
                    (mk⇔ (λ p → SL-≡ ha (Pointwise-≡⇒≡ p))
                         (λ where refl → ≡⇒Pointwise-≡ refl))
                    (DTO._≟_ (list sl₁) (list sl₂))
          ; _≤?_ = λ sl₁ sl₂ → DTO._≤?_ (list sl₁) (list sl₂)
          }
        }

  module Outer = SortedOps c-SortedList

  unions-helper : (X : Outer.SortedList) → Σ Inner.SortedList λ Y
    → ∀ {a} → (∃[ T ] T Outer.∈ˢ X × a Inner.∈ˢ T) ⇔ a Inner.∈ˢ Y
  unions-helper X = Inner.mkSorted (concat (L.map Inner.list (Outer.list X))) , λ {a} →
    (∃[ T ] T ∈ˡ Outer.list X × a ∈ˡ Inner.list T)
      ∼⟨ mk⇔ (λ (T , T∈X , a∈T) → ∈-concatMap⁺ Inner.list (lose T∈X a∈T))
              (∈-find ∘ ∈-concatMap⁻ Inner.list) ⟩
    a ∈ˡ concatMap Inner.list (Outer.list X)
      ∼⟨ Inner.∈-mkSorted⇔ ⟩
    a Inner.∈ˢ Inner.mkSorted (concat (L.map Inner.list (Outer.list X))) ∎
    where open R.EquationalReasoning


SortedList-Model : Theory {zeroˡ} {sucˡ zeroˡ}
SortedList-Model = let open Helpers in record
  { sc    = sorted-sc
  ; Set   = λ A ⦃ ca ⦄ → SortedOps.SortedList (getCstr ca)
  ; _∈_   = λ ⦃ ca ⦄ a sl → a ∈ˡ SortedOps.list sl
  ; sp    = Dec-SpecProperty
  ; c-Set = λ ⦃ ca ⦄ → mkCstr (c-SortedList ⦃ getCstr ca ⦄)
  ; specification = λ ⦃ ca ⦄ X P? →
      let open SortedOps (getCstr ca) in
      filterˢ P? X , mk⇔
        (λ where (Pa , a∈X) → ∈-filter⁺ P? a∈X Pa)
        (λ a∈f → swap (∈-filter⁻ P? a∈f))
  ; unions = λ ⦃ ca ⦄ X → unions-helper ⦃ getCstr ca ⦄ X
  ; replacement = λ ⦃ ca ⦄ ⦃ cb ⦄ f X →
      let module A = SortedOps (getCstr ca)
          module B = SortedOps (getCstr cb)
      in B.mkSorted (L.map f (A.list X)) , λ {b} → mk⇔
        (λ where (a , refl , a∈X) → to B.∈-mkSorted⇔ (∈-map⁺ f a∈X))
        (λ b∈Y → case ∈-map⁻ f (from B.∈-mkSorted⇔ b∈Y) of
          λ where (a , a∈X , refl) → (a , refl , a∈X))
  ; listing = λ ⦃ ca ⦄ l →
      let open SortedOps (getCstr ca) in
      mkSorted l , ∈-mkSorted⇔
  }
  where
    open Theory hiding (filter)
    open Equivalence
