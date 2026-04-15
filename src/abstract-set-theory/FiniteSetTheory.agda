{-# OPTIONS --safe #-}

module abstract-set-theory.FiniteSetTheory where

open import abstract-set-theory.Prelude

import Algebra
import Axiom.Set.List as L
open import Axiom.Set
open import Relation.Binary using (_Preserves_⟶_)

opaque
  List-Model : Theory {0ℓ}
  List-Model = L.List-Model
  List-Modelᶠ : Theoryᶠ
  List-Modelᶠ = L.List-Modelᶠ
  List-Modelᵈ : Theoryᵈ
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

module _ ⦃ _ : DecEq A ⦄ where
  open Restriction {A} ∈-sp public
    renaming (_∣_ to _∣ʳ_; _∣_ᶜ to _∣ʳ_ᶜ)

  open Corestriction {A} ∈-sp public
    renaming (_∣^_ to _∣^ʳ_; _∣^_ᶜ to _∣^ʳ_ᶜ) public

  open Restrictionᵐ {A} ∈-sp
    renaming (res-cong to resᵐ-cong) public
  open Corestrictionᵐ {A} ∈-sp
    renaming (cores-cong to coresᵐ-cong) public
  open Unionᵐ {A} ∈-sp public
  open Intersection {A} ∈-sp public
  open Lookupᵐ {A} ∈-sp public
  open Lookupᵐᵈ {A} ∈-sp public

module _ ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ where
  open Intersectionᵐ {A} {B} ∈-sp public
  open IndexedSumUnionᵐ {A} {B} ∈-sp (_∈? _) public

module Properties where
  open import Axiom.Set.Properties th public
  module _ ⦃ _ : DecEq A ⦄ where
    open Intersectionᵖ {A} ∈-sp public

opaque
  unfolding List-Model

  to-sp : {A : Type} (P : A → Type) → ⦃ P ⁇¹ ⦄ → specProperty (Theory.sp th) P
  to-sp _ = dec¹

  finiteness : ∀ (X : Theory.Set th A) → finite X
  finiteness = Theoryᶠ.finiteness List-Modelᶠ

  lengthˢ : ∀ {𝕊} ⦃ _ : DecEq A ⦄ ⦃ _ : IsSet 𝕊 A ⦄ → 𝕊 → ℕ
  lengthˢ X = Theoryᶠ.lengthˢ List-Modelᶠ (toSet X)

  lengthˢ-≡ᵉ :  ∀ {𝕊} ⦃ _ : DecEq A ⦄ ⦃ _ : IsSet 𝕊 A ⦄ → (X Y : 𝕊)
    → toSet X ≡ᵉ toSet Y
    → lengthˢ X ≡ lengthˢ Y
  lengthˢ-≡ᵉ X Y X≡Y =
    card-≡ᵉ (-, Theoryᶠ.DecEq⇒strongly-finite List-Modelᶠ (toSet X))
            (-, Theoryᶠ.DecEq⇒strongly-finite List-Modelᶠ (toSet Y)) X≡Y

  setToList : ℙ A → List A
  setToList = id

  instance
    DecEq-ℙ : ⦃ _ : DecEq A ⦄ → DecEq (ℙ A)
    DecEq-ℙ = L.Decˡ.DecEq-Set

    Show-ℙ : ⦃ _ : Show A ⦄ → Show (ℙ A)
    Show-ℙ .show = λ x → Show-finite .show (x , (finiteness x))

_ᶠᵐ : A ⇀ B → FinMap A B
(R , uniq) ᶠᵐ = (R , uniq , finiteness _)

_ᶠˢ : ℙ A → FinSet A
X ᶠˢ = X , finiteness _

filterˢ : (P : A → Type) ⦃ _ : P ⁇¹ ⦄ → ℙ A → ℙ A
filterˢ P = filterˢ? (to-sp P)

-- [ R ∘ʳ S ] = { (a , c) | ∃ b → (a , b) ∈ R × (b , c) ∈ S }
_∘ʳ_ : {A B C : Type} ⦃ _ : DecEq B ⦄ → Rel A B → Rel B C → Rel A C
R ∘ʳ S =
  concatMapˢ
    (λ (a , b) → mapˢ ((a ,_) ∘ proj₂) $ filterˢ ((b ≡_) ∘ proj₁) S)
    R

module _ {A B C : Type} ⦃ _ : DecEq B ⦄ {R R' : Rel A B} {S S' : Rel B C} where

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

filterᵐ : (P : A × B → Type) ⦃ _ : P ⁇¹ ⦄ → (A ⇀ B) → (A ⇀ B)
filterᵐ P = filterᵐ? (to-sp P)

filterKeys : (P : A → Type) ⦃ _ : P ⁇¹ ⦄ → (A ⇀ B) → (A ⇀ B)
filterKeys P = filterKeys? (to-sp P)

_∣^'_ : A ⇀ B → (P : B → Type) ⦃ _ : P ⁇¹ ⦄ → A ⇀ B
s ∣^' P = s ∣^'? to-sp P

indexedSumᵛ' : ⦃ DecEq A ⦄ → ⦃ DecEq B ⦄ → ⦃ CommutativeMonoid 0ℓ 0ℓ C ⦄ → (B → C) → A ⇀ B → C
indexedSumᵛ' f m = indexedSumᵛ f (m ᶠᵐ)

indexedSum' : ⦃ DecEq A ⦄ → ⦃ CommutativeMonoid 0ℓ 0ℓ B ⦄ → (A → B) → ℙ A → B
indexedSum' f s = indexedSum f (s ᶠˢ)

syntax indexedSumᵛ' (λ a → x) m = ∑[ a ← m ] x
syntax indexedSum'  (λ a → x) m = ∑ˢ[ a ← m ] x

module _ ⦃ _ : DecEq A ⦄ ⦃ _ : CommutativeMonoid 0ℓ 0ℓ C ⦄ where

  open CommutativeMonoid it

  module _ ⦃ _ : DecEq B ⦄ where

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
