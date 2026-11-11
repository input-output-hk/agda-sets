{-# OPTIONS --safe --no-import-sorts #-}

open import Axiom.Set

module Class.IsSet {ℓ} {ℓ_c} (th : Theory {ℓ} {ℓ_c}) where

open Theory th renaming (_∈_ to _∈ᵗ_; _∉_ to _∉ᵗ_)

import Axiom.Set.Rel th as Rel
open import Axiom.Set.Map th as Map
open import Axiom.Set.TotalMap th as TotalMap
open import Data.Product
open import abstract-set-theory.Prelude

private variable A B X : Type ℓ

record IsSet (A : Type ℓ) (B : Type ℓ) ⦃ _ : Cs B ⦄ : Type ℓ where
  field
    toSet : A → Set B

  infix 4 _∈_ _∉_
  _∈_ _∉_ : B → A → Type
  a ∈ X = a ∈ᵗ (toSet X)
  a ∉ X = a ∉ᵗ (toSet X)

open IsSet ⦃...⦄ public

infix 2 All-syntax
All-syntax : ∀ {A X} ⦃ _ : Cs A ⦄ ⦃ _ : IsSet X A ⦄ → (A → Type) → X → Type ℓ
All-syntax P X = All P (toSet X)
syntax All-syntax (λ x → P) l = ∀[ x ∈ l ] P

infix 2 Ex-syntax
Ex-syntax : ∀ {A X} ⦃ _ : Cs A ⦄ ⦃ _ : IsSet X A ⦄ → (A → Type) → X → Type ℓ
Ex-syntax P X = Any P (toSet X)
syntax Ex-syntax (λ x → P) l = ∃[ x ∈ l ] P

module _ ⦃ _ : Cs A ⦄ ⦃ _ : Cs B ⦄ ⦃ _ : IsSet X (A × B) ⦄ where
  dom : X → Set A
  dom = Rel.dom ∘ toSet

  range : X → Set B
  range = Rel.range ∘ toSet

instance
  IsSet-Set : ⦃ _ : Cs A ⦄ → IsSet (Set A) A
  IsSet-Set .toSet A = A

  IsSet-Map : ⦃ _ : Cs A ⦄ → ⦃ _ : Cs B ⦄ → IsSet (Map A B) (A × B)
  IsSet-Map .toSet = _ˢ

  IsSet-TotalMap : ⦃ _ : Cs A ⦄ → ⦃ _ : Cs B ⦄ → IsSet (TotalMap A B) (A × B)
  IsSet-TotalMap .toSet = TotalMap.rel
