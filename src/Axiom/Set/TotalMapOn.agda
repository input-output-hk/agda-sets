{-# OPTIONS --safe --no-import-sorts #-}

open import Axiom.Set using (Theory)

module Axiom.Set.TotalMapOn {ℓ} {ℓ_c} (th : Theory {ℓ} {ℓ_c}) where

open import abstract-set-theory.Prelude hiding (lookup; map)

open import Axiom.Set.Map th using (left-unique ; Map ; mapWithKey-uniq)
open import Axiom.Set.Rel th using (Rel ; dom ; dom∈)
open import Class.DecEq      using (DecEq ; _≟_)

open Theory th
open Equivalence  using (from)

private variable A B : Type ℓ

_TotalOn_ : ⦃ _ : Cs A ⦄ → ⦃ _ : Cs B ⦄ → Rel A B → Set A → Type ℓ
R TotalOn X = X ⊆ dom R


record TotalMapOn {A : Type ℓ} ⦃ _ : Cs A ⦄ (X : Set A) (B : Type ℓ) ⦃ _ : Cs B ⦄ : Type ℓ where
  field  rel              : Set (A × B)
         left-unique-rel  : left-unique rel
         total-rel        : rel TotalOn X

  toMap : Map A B
  toMap = rel , left-unique-rel

  lookup : Σ A (_∈ X) → B
  lookup (_ , a∈X) = proj₁ (from dom∈ (total-rel a∈X))

  -- verify that lookup is what we expect
  lookup∈rel : {a : A} (a∈X : a ∈ X) → (a , lookup (a , a∈X)) ∈ rel
  lookup∈rel a∈X = proj₂ (from dom∈ (total-rel a∈X))

  -- this is useful for proving equalities involving lookup
  rel⇒lookup : {a : A} {a∈dom : a ∈ X} {b : B} → (a , b) ∈ rel → lookup (a , a∈dom) ≡ b
  rel⇒lookup {a} {a∈dom} ab∈rel = sym (left-unique-rel ab∈rel (proj₂ (from dom∈ (total-rel a∈dom))))


module UpdateOn {B : Type ℓ} ⦃ _ : Cs A ⦄ ⦃ _ : Cs B ⦄ ⦃ _ : DecEq A ⦄ where

  private
    updateFn : A × B → A → B → B
    updateFn (a , b) x y with (x ≟ a)
    ... | yes  _ = b
    ... | no   _ = y

  open TotalMapOn

  mapWithKeyOn : {X : Set A}{B' : Type ℓ} ⦃ _ : Cs B' ⦄ → (A → B → B') → TotalMapOn X B → TotalMapOn X B'
  mapWithKeyOn f tm .rel              = map (λ{(x , y) → x , f x y}) (rel tm)
  mapWithKeyOn _ tm .left-unique-rel  = mapWithKey-uniq (left-unique-rel tm)
  mapWithKeyOn _ tm .total-rel a∈X    = ∈-map′ (∈-map′ (proj₂ (from dom∈ ((total-rel tm) a∈X))))

  -- Return a new total map which is the same as the given total map except at a.
  update : {X : Set A} → A → B → TotalMapOn X B → TotalMapOn X B
  update a b = mapWithKeyOn (updateFn (a , b))
