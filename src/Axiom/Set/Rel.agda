{-# OPTIONS --safe --no-import-sorts #-}
{-# OPTIONS -v allTactics:100 #-}

open import abstract-set-theory.Prelude hiding (map)
open import Axiom.Set using (Theory)

module Axiom.Set.Rel {ℓ} {ℓ_c} (th : Theory {ℓ} {ℓ_c}) where

import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Function.Related.Propositional as R

open Theory th
open import Axiom.Set.Properties {ℓ} {ℓ_c} th

import Data.Product as ×
open import Data.List.Ext.Properties using (_⊎-cong_)
open import Data.Maybe.Base using () renaming (map to map?)
open import Data.Product.Properties using (,-injectiveˡ; ×-≡,≡→≡; ×-≡,≡←≡)
open import Data.Product.Properties.Ext using (∃-cong′; ∃-distrib-⊎)
open import Relation.Unary using (Decidable)
open import Relation.Binary using (_Preserves_⟶_)

open import Tactic.AnyOf
open import Tactic.Defaults

open Equivalence

-- Because of missing macro hygiene, we have to copy&paste this.
-- c.f. https://github.com/agda/agda/issues/3819
private macro
  ∈⇒P = anyOfⁿᵗ
    (quote ∈-filter⁻' ∷ quote ∈-∪⁻ ∷ quote ∈-map⁻' ∷ quote ∈-fromList⁻ ∷ [])
  P⇒∈ = anyOfⁿᵗ
    (quote ∈-filter⁺' ∷ quote ∈-∪⁺ ∷ quote ∈-map⁺' ∷ quote ∈-fromList⁺ ∷ [])
  ∈⇔P = anyOfⁿᵗ
    ( quote ∈-filter⁻' ∷ quote ∈-∪⁻ ∷ quote ∈-map⁻' ∷ quote ∈-fromList⁻
    ∷ quote ∈-filter⁺' ∷ quote ∈-∪⁺ ∷ quote ∈-map⁺' ∷ quote ∈-fromList⁺ ∷ [])

Rel : (A B : Type ℓ) → ⦃ Cs A ⦄ → ⦃ Cs B ⦄ → Type ℓ
Rel A B = Set (A × B)

private variable A A' B B' C : Type ℓ

module _ ⦃ _ : Cs A ⦄ ⦃ _ : Cs B ⦄ where

  relatedˡ : Rel A B → Set A
  relatedˡ = map proj₁

  ∅ʳ : Rel A B
  ∅ʳ = ∅

  dom : Rel A B → Set A
  dom = map proj₁

  range : Rel A B → Set B
  range = map proj₂

  infix 10 _⁻¹ʳ
  _⁻¹ʳ : Rel A B → Rel B A
  R ⁻¹ʳ = map swap R
    where open import Data.Product using (swap)

  ⁻¹ʳ-cong : {R S : Rel A B}
           → R ≡ᵉ S → R ⁻¹ʳ ≡ᵉ S ⁻¹ʳ
  ⁻¹ʳ-cong = map-≡ᵉ

  disjoint-dom⇒disjoint : {R R' : Rel A B} → disjoint (dom R) (dom R') → disjoint R R'
  disjoint-dom⇒disjoint disj = ∈-map⁺'' -⟨ disj ⟩- ∈-map⁺''

  _∣'_ : {P : A → Type} → Rel A B → specProperty P → Rel A B
  m ∣' P? = filter (sp-∘ P? proj₁) m

  _∣^'_ : {P : B → Type} → Rel A B → specProperty P → Rel A B
  m ∣^' P? = filter (sp-∘ P? proj₂) m

  impl⇒res⊆ : ∀ {X : Rel A B} {P P'} (sp-P : specProperty P) (sp-P' : specProperty P')
            → (∀ {a} → P a → P' a) → X ∣' sp-P ⊆ X ∣' sp-P'
  impl⇒res⊆ sp-P sp-P' P⇒P' a∈X∣'P = ∈⇔P (×.map₁ P⇒P' (∈⇔P a∈X∣'P))

  impl⇒cores⊆ : ∀ {X : Rel A B} {P P'} (sp-P : specProperty P) (sp-P' : specProperty P')
              → (∀ {b} → P b → P' b) → X ∣^' sp-P ⊆ X ∣^' sp-P'
  impl⇒cores⊆ sp-P sp-P' P⇒P' a∈X∣^'P = ∈⇔P (×.map₁ P⇒P' (∈⇔P a∈X∣^'P))

  mapˡ : ⦃ _ : Cs A' ⦄ → (A → A') → Rel A B → Rel A' B
  mapˡ f R = map (×.map₁ f) R

  mapʳ : ⦃ _ : Cs B' ⦄ → (B → B') → Rel A B → Rel A B'
  mapʳ f R = map (×.map₂ f) R

  dom∈ : ∀ {R : Rel A B} {a} → (∃[ b ] (a , b) ∈ R) ⇔ a ∈ dom R
  dom∈ {R = R} {a} =
    (∃[ b ] (a , b) ∈ R)            ∼⟨ R.SK-sym (mk⇔ (λ { ((_ , y) , refl , ay∈R) → y , ay∈R })
                                                (λ (x , ax∈R) → (a , x) , refl , ax∈R)) ⟩
    (∃[ a₁ ] a ≡ proj₁ a₁ × a₁ ∈ R) ∼⟨ ∈-map ⟩

    a ∈ dom R                       ∎
    where open R.EquationalReasoning

  module _ {x : A} {y : B} where
    module _ {a : A} where
      ∈-dom-singleton-pair : a ≡ x ⇔ a ∈ dom ❴ x , y ❵
      ∈-dom-singleton-pair = mk⇔ (λ a≡x → to dom∈ (y , to ∈-singleton (×-≡,≡→≡ (a≡x , refl))))
                                 (,-injectiveˡ ∘ from ∈-singleton ∘ proj₂ ∘ from dom∈)

      dom-single→single : a ∈ dom ❴ x , y ❵ → a ∈ ❴ x ❵
      dom-single→single = to ∈-singleton ∘ from ∈-dom-singleton-pair

      single→dom-single : a ∈ ❴ x ❵ → a ∈ dom ❴ x , y ❵
      single→dom-single = to ∈-dom-singleton-pair ∘ from ∈-singleton

    dom-single≡single : dom ❴ x , y ❵ ≡ᵉ ❴ x ❵
    dom-single≡single = dom-single→single , single→dom-single

  ∈-dom : {a : A × B} {R : Rel A B} → a ∈ R → proj₁ a ∈ dom R
  ∈-dom {a = a} a∈ = to ∈-map (a , (refl , a∈))

  ∉-dom∅ : {a : A} → a ∉ dom (∅ {A = A × B})
  ∉-dom∅ {a} a∈dom∅ = ⊥-elim $ ∉-∅ $ proj₂ $ (from dom∈) a∈dom∅

  dom∅ : dom (∅ {A = A × B}) ≡ᵉ ∅
  dom∅ = ⊥-elim ∘ ∉-dom∅ , ∅-minimum (dom ∅)

  dom∪ : {R R' : Rel A B} → dom (R ∪ R') ≡ᵉ dom R ∪ dom R'
  dom∪ {R = R} {R'} = from ≡ᵉ⇔≡ᵉ' λ a →
    a ∈ dom (R ∪ R')                           ∼⟨ R.SK-sym dom∈ ⟩
    (∃[ b ] (a , b) ∈ R ∪ R')                  ∼⟨ ∃-cong′ (R.SK-sym ∈-∪) ⟩
    (∃[ b ] ((a , b) ∈ R ⊎ (a , b) ∈ R'))      ↔⟨ ∃-distrib-⊎ ⟩
    (∃[ b ] (a , b) ∈ R ⊎ ∃[ b ] (a , b) ∈ R') ∼⟨ dom∈ ⊎-cong dom∈ ⟩
    (a ∈ dom R ⊎ a ∈ dom R')                   ∼⟨ ∈-∪ ⟩
    a ∈ dom R ∪ dom R'                         ∎
    where open R.EquationalReasoning

  dom⊆ : dom Preserves _⊆_ ⟶ _⊆_
  dom⊆ R⊆R' a∈ = to dom∈ $ proj₁ (from dom∈ a∈) , R⊆R' (proj₂ (from dom∈ a∈))

  dom-cong : {R R' : Rel A B} → R ≡ᵉ R' → dom R ≡ᵉ dom R'
  dom-cong RR' = (dom⊆ (proj₁ RR')) , (dom⊆ (proj₂ RR'))

dom-⊆mapʳ : ⦃ _ : Cs A ⦄ ⦃ _ : Cs B ⦄ ⦃ _ : Cs B' ⦄
  → {R : Rel A B} {f : B → B'} → dom R ⊆ dom (mapʳ f R)
dom-⊆mapʳ {f = f} {a} a∈domR with from dom∈ a∈domR
... | b , ab∈R = to dom∈ (f b , to ∈-map ((a , b) , refl , ab∈R))

dom-mapʳ⊆ : ⦃ _ : Cs A ⦄ ⦃ _ : Cs B ⦄ ⦃ _ : Cs B' ⦄
  → {R : Rel A B} {f : B → B'} → dom (mapʳ f R) ⊆ dom R
dom-mapʳ⊆ a∈dmR with from dom∈ a∈dmR
... | _ , p∈map with from ∈-map p∈map
... | (_ , b) , refl , ab∈R = to dom∈ (b , ab∈R)

mapʳ-dom : ⦃ _ : Cs A ⦄ ⦃ _ : Cs B ⦄ ⦃ _ : Cs B' ⦄
  → {R : Rel A B} {f : B → B'} → dom R ≡ᵉ dom (mapʳ f R)
mapʳ-dom = dom-⊆mapʳ , dom-mapʳ⊆

dom-mapˡ≡map-dom : ⦃ _ : Cs A ⦄ ⦃ _ : Cs B ⦄ ⦃ _ : Cs A' ⦄
  → {R : Rel A B} {f : A → A'} → dom (mapˡ f R) ≡ᵉ map f (dom R)
dom-mapˡ≡map-dom .proj₁ a'∈dom with from ∈-map (proj₂ (from dom∈ a'∈dom))
... | (a , b) , a'b≡fab , ab∈R = to ∈-map (a , proj₁ (×-≡,≡←≡ a'b≡fab) , to dom∈ (b , ab∈R))
dom-mapˡ≡map-dom .proj₂ a'∈map with from ∈-map a'∈map
... | a , a'≡fa , a∈domR with from dom∈ a∈domR
... | b , ab∈R = to dom∈ (b , to ∈-map ((a , b) , ×-≡,≡→≡ (a'≡fa , refl) , ab∈R))

module _ ⦃ _ : Cs A ⦄ ⦃ _ : Cs B ⦄ where

  dom-∅ : {R : Rel A B} → dom R ⊆ ∅ → R ≡ᵉ ∅
  dom-∅ dom⊆∅ = ∅-least (λ {x} x∈R → ⊥-elim $ ∉-∅ $ dom⊆∅ $ to dom∈ (-, x∈R))

  mapPartialLiftKey : (A → B → Maybe B') → A × B → Maybe (A × B')
  mapPartialLiftKey f (k , v) = map? (k ,_) (f k v)

  mapPartialLiftKey-map : ⦃ _ : Cs B' ⦄
    → ∀ {a : A} {b' : B'} {f : A → B → Maybe B'} {r : Rel A B}
    → just (a , b') ∈ map (mapPartialLiftKey f) r
    → ∃[ b ] just b' ≡ f a b × (a , b) ∈ r
  mapPartialLiftKey-map {f = f} ab∈m
    with from ∈-map ab∈m
  ... | (a' , b') , ≡ , a'b'∈r
    with f a' b' in eq
  mapPartialLiftKey-map {f = f} ab∈m | (a' , b') , refl , a'b'∈r | just x
    = b' , sym eq , a'b'∈r

  mapMaybeWithKey : ⦃ _ : Cs B' ⦄ → (A → B → Maybe B') → Rel A B → Rel A B'
  mapMaybeWithKey f r = mapPartial (mapPartialLiftKey f) r

  ∈-mapMaybeWithKey : ⦃ _ : Cs B' ⦄
    → ∀ {a : A} {b' : B'} {f : A → B → Maybe B'} {r : Rel A B}
    → (a , b') ∈ mapMaybeWithKey f r
    → ∃[ b ] (just b' ≡ f a b × (a , b) ∈ r)
  ∈-mapMaybeWithKey {a = a} {b'} {f} ab'∈
    = mapPartialLiftKey-map {f = f}
    $ ⊆-mapPartial
    $ to (∈-map {f = just}) ((a , b') , refl , ab'∈)

  module Restriction (sp-∈ : spec-∈ A) where

    _∣_ : Rel A B → Set A → Rel A B
    m ∣ X = m ∣' sp-∈ {X}

    _∣_ᶜ : Rel A B → Set A → Rel A B
    m ∣ X ᶜ = m ∣' sp-¬ (sp-∈ {X})

    _⟪$⟫_ : Rel A B → Set A → Set B
    m ⟪$⟫ X = range (m ∣ X)

    res-cong : {R : Rel A B} → (R ∣_) Preserves _≡ᵉ_ ⟶ _≡ᵉ_
    res-cong (X⊆Y , Y⊆X) = (λ ∈R∣X → ∈⇔P (×.map₁ X⊆Y (∈⇔P ∈R∣X)))
                         , (λ ∈R∣Y → ∈⇔P (×.map₁ Y⊆X (∈⇔P ∈R∣Y)))

    res-dom : {R : Rel A B} {X : Set A} → dom (R ∣ X) ⊆ X
    res-dom a∈dom with ∈⇔P a∈dom
    ... | _ , refl , h = proj₁ $ ∈⇔P h

    res-domᵐ : {R : Rel A B} {X : Set A} → dom (R ∣ X) ⊆ dom R
    res-domᵐ a∈dom with ∈⇔P a∈dom
    ... | _ , refl , h = ∈-map⁺'' $ proj₂ (∈⇔P h)

    res-comp-cong : {R : Rel A B} → (R ∣_ᶜ) Preserves _≡ᵉ_ ⟶ _≡ᵉ_
    res-comp-cong (X⊆Y , Y⊆X) = (λ ∈R∣X → ∈⇔P (×.map₁ (_∘ Y⊆X) (∈⇔P ∈R∣X)))
                              , (λ ∈R∣Y → ∈⇔P (×.map₁ (_∘ X⊆Y) (∈⇔P ∈R∣Y)))

    res-comp-dom : {R : Rel A B} {X : Set A} → ∀ {a} → a ∈ dom (R ∣ X ᶜ) → a ∉ X
    res-comp-dom a∈dom with ∈⇔P a∈dom
    ... | _ , refl , h = proj₁ $ ∈⇔P h

    res-comp-domᵐ : {R : Rel A B} {X : Set A} → dom (R ∣ X ᶜ) ⊆ dom R
    res-comp-domᵐ a∈dom with ∈⇔P a∈dom
    ... | _ , refl , h = ∈-map⁺'' (proj₂ (∈⇔P h))

    res-⊆ : {R : Rel A B} {X : Set A} → (R ∣ X) ⊆ R
    res-⊆ = proj₂ ∘′ ∈⇔P

    ex-⊆ : {R : Rel A B} {X : Set A} → (R ∣ X ᶜ) ⊆ R
    ex-⊆ = proj₂ ∘′ ∈⇔P

    res-∅ : {R : Rel A B} → R ∣ ∅ ≡ᵉ ∅
    res-∅ = dom-∅ res-dom

    res-∅ᶜ : {R : Rel A B} → R ∣ ∅ ᶜ ≡ᵉ R
    res-∅ᶜ = ex-⊆ , λ a∈R → ∈⇔P (∉-∅ , a∈R)

    ∈-res : {R : Rel A B} {X : Set A} → ∀ {a} {b : B} → (a , b) ∈ (R ∣ X) ⇔ ((a , b) ∈ R × a ∈ X)
    ∈-res =
      mk⇔ (λ ab∈ → (res-⊆ ab∈ , res-dom (to dom∈ (_ , ab∈))))
          (to ∈-filter ∘ ×.swap)

    ∈-resᶜ-dom⁻ : {R : Rel A B} {X : Set A} → ∀ {a} → a ∈ dom (R ∣ X ᶜ) → a ∉ X × ∃[ b ] (a , b) ∈ R
    ∈-resᶜ-dom⁻ a∈ = res-comp-dom a∈ , from dom∈ (dom⊆ ex-⊆ a∈)

    ∈-resᶜ-dom⁺ : {R : Rel A B} {X : Set A} → ∀ {a} → a ∉ X × ∃[ b ] (a , b) ∈ R → a ∈ dom (R ∣ X ᶜ)
    ∈-resᶜ-dom⁺ (a∉X , (b , ab∈R)) = to dom∈ (b , (∈⇔P (a∉X , ab∈R)))

    ∈-resᶜ-dom : {R : Rel A B} {X : Set A} → ∀ {a} → a ∈ dom (R ∣ X ᶜ) ⇔ (a ∉ X × ∃[ b ] (a , b) ∈ R)
    ∈-resᶜ-dom = mk⇔ ∈-resᶜ-dom⁻ ∈-resᶜ-dom⁺

    res-ex-∪ : {R : Rel A B} {X : Set A} → Decidable (_∈ X) → (R ∣ X) ∪ (R ∣ X ᶜ) ≡ᵉ R
    res-ex-∪ ∈X? = ∪-⊆ res-⊆ ex-⊆ , λ {a} h → case ∈X? (proj₁ a) of λ where
      (yes p) → ∈⇔P (inj₁ (∈⇔P (p , h)))
      (no ¬p) → ∈⇔P (inj₂ (∈⇔P (¬p , h)))

    res-ex-disjoint : {R : Rel A B} {X : Set A} → disjoint (dom (R ∣ X)) (dom (R ∣ X ᶜ))
    res-ex-disjoint h h' = res-comp-dom h' (res-dom h)

    res-ex-disj-∪ : {R : Rel A B} {X : Set A} → Decidable (_∈ X) → R ≡ (R ∣ X) ⨿ (R ∣ X ᶜ)
    res-ex-disj-∪ ∈X? = IsEquivalence.sym ≡ᵉ-isEquivalence (res-ex-∪ ∈X?)
                      , disjoint-dom⇒disjoint res-ex-disjoint
      where open import Relation.Binary using (IsEquivalence)

    curryʳ : ⦃ _ : Cs C ⦄ → Rel (A × B) C → A → Rel B C
    curryʳ R a = map (×.map₁ proj₂) (filter (sp-∘ (sp-∘ (sp-∈ {❴ a ❵}) proj₁) proj₁) R)

    ∈-curryʳ : ⦃ _ : Cs C ⦄ → ∀ {a} {b : B} {c : C} {R : Rel (A × B) C} → (b , c) ∈ curryʳ R a → ((a , b) , c) ∈ R
    ∈-curryʳ h = case ∈⇔P h of λ where
      (((a , b) , c) , refl , h'') → case ∈⇔P h'' of λ where
        (p , p') → case from ∈-singleton p of λ where refl → p'

    open Intersection sp-∈
    open Intersectionᵖ sp-∈

    module _ ⦃ _ : Cs C ⦄ where
      private
        domᶜ : Rel A C → Set A
        domᶜ = map proj₁

        -- Restriction for Rel A C (can't reuse _∣_ which is fixed to Rel A B)
        _∣ᶜ_ : Rel A C → Set A → Rel A C
        m' ∣ᶜ X = filter (sp-∘ (sp-∈ {X}) proj₁) m'

      res-dom-comm⊆∩ : {m : Rel A B} {m' : Rel A C} → dom (m ∣ domᶜ m') ⊆ dom m ∩ domᶜ m'
      res-dom-comm⊆∩ x = to ∈-∩ (res-domᵐ x , res-dom x)

      res-dom-comm∩⊆ : {m : Rel A B} {m' : Rel A C} → dom m ∩ domᶜ m' ⊆ dom (m ∣ domᶜ m')
      res-dom-comm∩⊆ {m = m} {m' = m'} x with from ∈-∩ x
      ... | a∈dm , a∈dm' with from dom∈ a∈dm | from dom∈ a∈dm'
      ... | b , ab∈m | c , ac∈m = to dom∈ (b , to ∈-filter (a∈dm' , ab∈m))

      res-dom-comm' : {m : Rel A B} {m' : Rel A C} → dom (m ∣ domᶜ m') ≡ᵉ dom m ∩ domᶜ m'
      res-dom-comm' = res-dom-comm⊆∩ , res-dom-comm∩⊆

      res-dom-comm : {m : Rel A B} {m' : Rel A C} → dom (m ∣ domᶜ m') ≡ᵉ domᶜ (m' ∣ᶜ dom m)
      res-dom-comm {m = m} {m'} = fwd , bwd
        where
          fwd : dom (m ∣ domᶜ m') ⊆ domᶜ (m' ∣ᶜ dom m)
          fwd x with from dom∈ (res-domᵐ x) | res-dom x
          ... | b , ab∈m | a∈dm' with from dom∈ a∈dm'
          ... | c , ac∈m' = to dom∈ (c , to ∈-filter (to dom∈ (b , ab∈m) , ac∈m'))

          bwd : domᶜ (m' ∣ᶜ dom m) ⊆ dom (m ∣ domᶜ m')
          bwd x with from ∈-map x
          ... | p , refl , p∈filt with from ∈-filter p∈filt
          ... | a∈dm , ac∈m' with from dom∈ a∈dm
          ... | b , ab∈m = to dom∈ (b , to ∈-filter (to dom∈ (_ , ac∈m') , ab∈m))

  module Corestriction (sp-∈ : spec-∈ B) where

    _∣^_ : Rel A B → Set B → Rel A B
    m ∣^ X = m ∣^' sp-∈ {X}

    _∣^_ᶜ : Rel A B → Set B → Rel A B
    m ∣^ X ᶜ = m ∣^' sp-¬ (sp-∈ {X})

    cores-⊆ : {R : Rel A B} {X : Set B} → (R ∣^ X) ⊆ R
    cores-⊆ = proj₂ ∘′ ∈⇔P

    coex-⊆ : {R : Rel A B} {X : Set B} → (R ∣^ X ᶜ) ⊆ R
    coex-⊆ = proj₂ ∘′ ∈⇔P

    cores-cong : ∀ {R Q : Rel A B} {X Y : Set B}
               → X ⊆ Y → R ⊆ Q
               → R ∣^ X ⊆ Q ∣^ Y
    cores-cong X⊆Y R⊆Y p with from ∈-filter p
    ... | (q , p) = to ∈-filter (X⊆Y q , R⊆Y p)
