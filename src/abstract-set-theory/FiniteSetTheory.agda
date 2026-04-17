{-# OPTIONS --safe #-}

module abstract-set-theory.FiniteSetTheory where

open import abstract-set-theory.Prelude

import Algebra
import Axiom.Set.List as L
open import Axiom.Set
open import Relation.Binary using (_Preserves_⟶_)

opaque
  List-Model : Theory {0ℓ} {0ℓ}
  List-Model = L.List-Model
  List-Modelᶠ : Theoryᶠ {0ℓ}
  List-Modelᶠ = L.List-Modelᶠ
  List-Modelᵈ : Theoryᵈ {0ℓ}
  List-Modelᵈ = L.List-Modelᵈ

private variable
  A A' B C : Set

open Theoryᵈ List-Modelᵈ public
  renaming (Set to ℙ_; filter to filterˢ?; map to mapˢ; ∅ to ∅ˢ; ❴_❵ to ❴_❵ˢ)
  hiding (_∈_; _∉_)

open import Axiom.Set.Map th public
  renaming ( Map to infixr 1 _⇀_
           ; filterᵐ to filterᵐ?; filterKeys to filterKeys?; _∣^'_ to _∣^'?_ )

open import Axiom.Set.Factor List-Model public
open import Axiom.Set.Map.Dec List-Modelᵈ public
open import Axiom.Set.Properties th using (≡ᵉ-isEquivalence)
open import Axiom.Set.Rel th public hiding (_∣'_; _∣^'_; dom; range)
open import Axiom.Set.Sum th public
open import Axiom.Set.TotalMap th public
open import Axiom.Set.TotalMapOn th
open import Class.IsSet th public
open import Class.HasEmptySet th public
open import Class.HasSingleton th public

open import Axiom.Set.Properties th using (card-≡ᵉ)

infixr 9 _∘ʳ_

module _ ⦃ _ : Cs A ⦄ ⦃ _ : DecEq A ⦄ where
  private module R' {B} ⦃ _ : Cs B ⦄ = Restriction {A} {B} ∈-sp
  open R' public
    renaming (_∣_ to _∣ʳ_; _∣_ᶜ to _∣ʳ_ᶜ)

  private module CR' {B} ⦃ _ : Cs B ⦄ ⦃ _ : DecEq B ⦄ = Corestriction {A} {B} (∈-sp {B})
  open CR' public
    renaming (_∣^_ to _∣^ʳ_; _∣^_ᶜ to _∣^ʳ_ᶜ)

  private module Rᵐ' {B} ⦃ _ : Cs B ⦄ = Restrictionᵐ {A} {B} ∈-sp
  open Rᵐ' public
    renaming (res-cong to resᵐ-cong)

  private module CRᵐ' {B} ⦃ _ : Cs B ⦄ ⦃ _ : DecEq B ⦄ = Corestrictionᵐ {A} {B} (∈-sp {B})
  open CRᵐ' public
    renaming (cores-cong to coresᵐ-cong)

  open Unionᵐ {A} ∈-sp public
  open Intersection {A} ∈-sp public
  open Lookupᵐᵈ {A} ∈-sp public

module _ ⦃ _ : Cs A ⦄ ⦃ _ : Cs B ⦄ ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ where
  open Intersectionᵐ {A} {B} ∈-sp public
  open IndexedSumUnionᵐ {A} {B} ∈-sp (_∈? _) public

module Properties where
  open import Axiom.Set.Properties th public
  module _ ⦃ _ : Cs A ⦄ ⦃ _ : DecEq A ⦄ where
    open Intersectionᵖ {A} ∈-sp public

opaque
  unfolding List-Model List-Modelᶠ List-Modelᵈ

  to-sp : {A : Type} (P : A → Type) → ⦃ P ⁇¹ ⦄ → specProperty P
  to-sp _ = dec¹

  finiteness : ⦃ _ : Cs A ⦄ → ∀ (X : Theory.Set th A) → finite X
  finiteness = Theoryᶠ.finiteness List-Modelᶠ

  lengthˢ : ∀ {𝕊} ⦃ _ : Cs A ⦄ ⦃ _ : DecEq A ⦄ ⦃ _ : IsSet 𝕊 A ⦄ → 𝕊 → ℕ
  lengthˢ X = Theoryᶠ.lengthˢ List-Modelᶠ (toSet X)

  lengthˢ-≡ᵉ :  ∀ {𝕊} ⦃ _ : Cs A ⦄ ⦃ _ : DecEq A ⦄ ⦃ _ : IsSet 𝕊 A ⦄ → (X Y : 𝕊)
    → toSet X ≡ᵉ toSet Y
    → lengthˢ X ≡ lengthˢ Y
  lengthˢ-≡ᵉ X Y X≡Y =
    card-≡ᵉ (-, Theoryᶠ.DecEq⇒strongly-finite List-Modelᶠ (toSet X))
            (-, Theoryᶠ.DecEq⇒strongly-finite List-Modelᶠ (toSet Y)) X≡Y

  setToList : ⦃ _ : Cs A ⦄ → ℙ A → List A
  setToList = id

  instance
    DecEq-ℙ : ⦃ _ : Cs A ⦄ → ⦃ _ : DecEq A ⦄ → DecEq (ℙ A)
    DecEq-ℙ = L.Decˡ.DecEq-Set

    Show-ℙ : ⦃ _ : Cs A ⦄ → ⦃ _ : Show A ⦄ → Show (ℙ A)
    Show-ℙ .show = λ x → Show-finite .show (x , (finiteness x))

_ᶠᵐ : ⦃ _ : Cs A ⦄ → ⦃ _ : Cs B ⦄ → A ⇀ B → FinMap A B
(R , uniq) ᶠᵐ = (R , uniq , finiteness _)

_ᶠˢ : ⦃ _ : Cs A ⦄ → ℙ A → FinSet A
X ᶠˢ = X , finiteness _

filterˢ : ⦃ _ : Cs A ⦄ → (P : A → Type) ⦃ _ : P ⁇¹ ⦄ → ℙ A → ℙ A
filterˢ P = filterˢ? (to-sp P)

-- [ R ∘ʳ S ] = { (a , c) | ∃ b → (a , b) ∈ R × (b , c) ∈ S }
_∘ʳ_ : {A B C : Type} ⦃ _ : Cs A ⦄ ⦃ _ : Cs B ⦄ ⦃ _ : Cs C ⦄ ⦃ _ : DecEq B ⦄ → Rel A B → Rel B C → Rel A C
R ∘ʳ S =
  concatMapˢ
    (λ (a , b) → mapˢ ((a ,_) ∘ proj₂) $ filterˢ ((b ≡_) ∘ proj₁) S)
    R

module _ {A B C : Type} ⦃ _ : Cs A ⦄ ⦃ _ : Cs B ⦄ ⦃ _ : Cs C ⦄ ⦃ _ : DecEq B ⦄ {R R' : Rel A B} {S S' : Rel B C} where

  open Equivalence

  ∘ʳ-cong : R ≡ᵉ R' → S ≡ᵉ S'
          → R ∘ʳ S  ≡ᵉ R' ∘ʳ S'
  ∘ʳ-cong R≡R' S≡S' = ∘ʳ-cong-⊆ , ∘ʳ-cong-⊇
    where ∘ʳ-cong-⊆ : R ∘ʳ S  ⊆ R' ∘ʳ S'
          ∘ʳ-cong-⊆ p with from ∈-concatMapˢ p
          ... | (a , a∈R , p) with from ∈-map p
          ... | _ , refl , p with from ∈-filter p
          ... | (p , q) = to ∈-concatMapˢ (a , R≡R' .proj₁ a∈R , to ∈-map (_ , (refl , to ∈-filter (p , S≡S' .proj₁ q))))

          ∘ʳ-cong-⊇ : R' ∘ʳ S'  ⊆ R ∘ʳ S
          ∘ʳ-cong-⊇ p with from ∈-concatMapˢ p
          ... | (a , a∈R , p) with from ∈-map p
          ... | _ , refl , p with from ∈-filter p
          ... | (p , q) = to ∈-concatMapˢ (a , R≡R' .proj₂ a∈R , to ∈-map (_ , (refl , to ∈-filter (p , S≡S' .proj₂ q))))

filterᵐ : ⦃ _ : Cs A ⦄ → ⦃ _ : Cs B ⦄ → (P : A × B → Type) ⦃ _ : P ⁇¹ ⦄ → (A ⇀ B) → (A ⇀ B)
filterᵐ P = filterᵐ? (to-sp P)

filterKeys : ⦃ _ : Cs A ⦄ → ⦃ _ : Cs B ⦄ → (P : A → Type) ⦃ _ : P ⁇¹ ⦄ → (A ⇀ B) → (A ⇀ B)
filterKeys P = filterKeys? (to-sp P)

_∣^'_ : ⦃ _ : Cs A ⦄ → ⦃ _ : Cs B ⦄ → A ⇀ B → (P : B → Type) ⦃ _ : P ⁇¹ ⦄ → A ⇀ B
s ∣^' P = s ∣^'? to-sp P

indexedSumᵛ' : ⦃ _ : Cs A ⦄ → ⦃ _ : Cs B ⦄ → ⦃ DecEq A ⦄ → ⦃ DecEq B ⦄ → ⦃ CommutativeMonoid 0ℓ 0ℓ C ⦄ → (B → C) → A ⇀ B → C
indexedSumᵛ' f m = indexedSumᵛ f (m ᶠᵐ)

indexedSum' : ⦃ _ : Cs A ⦄ → ⦃ DecEq A ⦄ → ⦃ CommutativeMonoid 0ℓ 0ℓ B ⦄ → (A → B) → ℙ A → B
indexedSum' f s = indexedSum f (s ᶠˢ)

syntax indexedSumᵛ' (λ a → x) m = ∑[ a ← m ] x
syntax indexedSum'  (λ a → x) m = ∑ˢ[ a ← m ] x

module _ ⦃ _ : Cs A ⦄ ⦃ _ : Cs C ⦄ ⦃ _ : DecEq A ⦄ ⦃ _ : CommutativeMonoid 0ℓ 0ℓ C ⦄ where

  open CommutativeMonoid it

  module _ ⦃ _ : Cs B ⦄ ⦃ _ : DecEq B ⦄ where

    aggregateBy : ⦃ DecEq C ⦄ → Rel A B → A ⇀ C → B ⇀ C
    aggregateBy R m =
      mapFromFun (λ b → ∑[ x ← m ∣ dom (R ∣^ʳ ❴ b ❵) ] x) (range R)

    indexedSumᵛ'-cong
      : ∀ {f : B → C} → indexedSumᵛ' f Preserves _≡ᵉ_ on proj₁ ⟶ _≈_
    indexedSumᵛ'-cong {x = x} {y} =
      indexedSum-cong {A = A × B} {x = (x ˢ) ᶠˢ} {(y ˢ) ᶠˢ}

  indexedSumᵐ-∪ˡ-∪ˡᶠ
    : ∀ ⦃ _ : DecEq C ⦄ (m : A ⇀ C) (m' : A ⇀ C)
    → indexedSumᵐ proj₂ ((m ∪ˡ m') ᶠᵐ) ≈ indexedSumᵐ proj₂ ((m ᶠᵐ) ∪ˡᶠ (m' ᶠᵐ))
  indexedSumᵐ-∪ˡ-∪ˡᶠ m m' =
      indexedSumᵐ-cong
        {f = proj₂}
        {x = (m ∪ˡ m') ᶠᵐ}
        {y = (m ᶠᵐ) ∪ˡᶠ (m' ᶠᵐ)}
        ≡ᵉ.refl
    where
      open import Relation.Binary.Structures using (IsEquivalence)
      module ≡ᵉ = IsEquivalence ≡ᵉ-isEquivalence
