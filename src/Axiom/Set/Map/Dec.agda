{-# OPTIONS --safe --no-import-sorts #-}
open import Axiom.Set using (Theoryᵈ; Theory)

module Axiom.Set.Map.Dec (thᵈ : Theoryᵈ) where

open import abstract-set-theory.Prelude hiding (map; Monoid)

import Data.Sum as Sum
open import Data.These hiding (map)

open Theoryᵈ thᵈ using (_∈?_; ∈-sp; th; incl-set'; incl-set; incl-set-proj₁⊇)
open Theory th
open import Axiom.Set.Rel th using (Rel; dom; dom∈; dom∪)
open import Axiom.Set.Map th
open import Axiom.Set.Properties th using (∈-∪⁺; ∈-∪⁻; ∪-⊆ˡ)
open import Data.Product.Properties using (×-≡,≡→≡; ×-≡,≡←≡)

open Equivalence

private variable A B C D : Type

module Lookupᵐᵈ (sp-∈ : spec-∈ A) where
  open Lookupᵐ sp-∈
  open Unionᵐ sp-∈

  unionThese : ⦃ DecEq A ⦄ → (m : Map A B) (m' : Map A C) (x : A)
    → x ∈ dom (m ˢ) ∪ dom (m' ˢ) → These B C
  unionThese m m' x dp with x ∈? dom (m ˢ) | x ∈? dom (m' ˢ)
  ... | yes mr | yes mr' = these (lookupᵐ m x) (lookupᵐ m' x)
  ... | yes mr | no  mr' = this  (lookupᵐ m x)
  ... | no  mr | yes mr' = that  (lookupᵐ m' x)
  ... | no  mr | no  mr' = Sum.[ flip contradiction mr , flip contradiction mr' ]
                               (from ∈-∪ dp)

  unionWith : ⦃ DecEq A ⦄ → (These B C → D) → Map A B → Map A C → Map A D
  unionWith f m@(r , p) m'@(r' , p') = m'' , helper
     where
       d = dom r ∪ dom r'
       m'' = map (λ (x , p) → x , f (unionThese m m' x p)) (incl-set d)

       helper : left-unique m''
       helper q q'
         with _ , refl , t  ← from ∈-map q
         with _ , refl , t' ← from ∈-map q'
         with from (∈-mapPartial {f = incl-set' _}) t
            | from (∈-mapPartial {f = incl-set' _}) t'
       ... | z , _ | z' , _
         with z ∈? d in eq | z' ∈? d in eq'
       helper _ _ | _ , _ , refl | _ , _ , refl | yes _ | yes _
         with refl ← trans (sym eq) eq' = refl

  intersectionWith
    : (B → C → D)
    → (m : Map A B) ⦃ _ : ∀ {x} → (x ∈ dom (m ˢ)) ⁇ ⦄
    → Map A C
    → Map A D
  intersectionWith f m = mapMaybeWithKeyᵐ (λ a c → flip f c <$> lookupᵐ? m a)

  module _ {V : Type} ⦃ mon : CommutativeMonoid 0ℓ 0ℓ V ⦄ ⦃ _ : DecEq A ⦄ where
    infixr 6 _∪⁺_
    open CommutativeMonoid mon

    _∪⁺_ : Map A V → Map A V → Map A V
    _∪⁺_ = unionWith (fold id id _◇_)

    aggregate₊ : FinSet (A × V) → Map A V
    aggregate₊ (_ , l , _) = foldl (λ m x → m ∪⁺ ❴ x ❵ᵐ) ∅ᵐ l

    module _ {m m' : Map A V} where
      ∪dom-lookup : ∃[ a ] a ∈ dom (m ˢ) ∪ dom (m' ˢ) → A × V
      ∪dom-lookup (a , a∈) = a , (fold id id _◇_)(unionThese m m' a a∈)

      dom∪⁺⊆∪dom : dom ((m ∪⁺ m') ˢ) ⊆ dom (m ˢ) ∪ dom (m' ˢ)
      dom∪⁺⊆∪dom {a} a∈ = subst (_∈ dom (m ˢ) ∪ dom (m' ˢ))
                                  (sym $ proj₁ (×-≡,≡←≡ $ proj₁ (proj₂ ∈-dom∪⁺)))
                                  (proj₂ $ proj₁ ∈-dom∪⁺)
        where
        ∈-dom∪⁺ : ∃[ c ] (a , proj₁ (from dom∈ a∈)) ≡ ∪dom-lookup c
                          × c ∈ incl-set (dom (m ˢ) ∪ dom (m' ˢ))
        ∈-dom∪⁺ = from ∈-map $ proj₂ $ from dom∈ a∈

      ∪dom⊆dom∪⁺ : dom (m ˢ) ∪ dom (m' ˢ) ⊆ dom ((m ∪⁺ m') ˢ)
      ∪dom⊆dom∪⁺ {a} a∈ with from ∈-map (incl-set-proj₁⊇ a∈)
      ... | c' , a≡c₁' , c'∈ =
        to dom∈ (proj₂ (∪dom-lookup c') , to ∈-map (c' , ×-≡,≡→≡ (a≡c₁' , refl) , c'∈))

      dom∪⁺⇔∪dom : ∀ {a} → a ∈ dom ((m ∪⁺ m')ˢ) ⇔ a ∈ dom (m ˢ) ∪ dom (m' ˢ)
      dom∪⁺⇔∪dom {a} = mk⇔ dom∪⁺⊆∪dom ∪dom⊆dom∪⁺

      dom∪⁺≡∪dom : dom ((m ∪⁺ m')ˢ) ≡ᵉ dom (m ˢ) ∪ dom (m' ˢ)
      dom∪⁺≡∪dom = to dom∪⁺⇔∪dom , from dom∪⁺⇔∪dom


      open import Function.Reasoning

      private
        rhs-∪ˡ : Rel A V
        rhs-∪ˡ = (filterᵐ (sp-∘ (sp-¬ (sp-∈ {X = dom (m ˢ)})) proj₁) m') ˢ

      dom∪ˡˡ : dom (m ˢ) ⊆ dom ((m ∪ˡ m') ˢ)
      dom∪ˡˡ {a} a∈ = a∈ ∶
          a ∈ dom (m ˢ)               |> ∪-⊆ˡ ∶
          a ∈ dom (m ˢ) ∪ dom rhs-∪ˡ  |> proj₂ dom∪ ∶
          a ∈ dom ((m ˢ) ∪ rhs-∪ˡ)    |> id ∶
          a ∈ dom ((m ∪ˡ m') ˢ)

      dom∪ˡʳ : dom (m' ˢ) ⊆ dom ((m ∪ˡ m') ˢ)
      dom∪ˡʳ {a} a∈ with a ∈? dom (m ˢ)
      ... | yes p = dom∪ˡˡ p
      ... | no ¬p = a∈ ∶
          a ∈ dom (m' ˢ)                        |> from ∈-map ∶
          (∃[ ab ] a ≡ proj₁ ab × ab ∈ (m' ˢ))  |>′
             (λ { (ab , refl , ab∈m') → (¬p , ab∈m') ∶
                 (a ∉ dom (m ˢ) × ab ∈ (m' ˢ))  |> to ∈-filter ∶
                 ab ∈ rhs-∪ˡ                    |> (λ ab∈f → to ∈-map (ab , refl , ab∈f)) ∶
                 a ∈ dom rhs-∪ˡ
             }) ∶
          a ∈ dom rhs-∪ˡ              |> ∈-∪⁺ ∘ inj₂ ∶
          a ∈ dom (m ˢ) ∪ dom rhs-∪ˡ  |> proj₂ dom∪ ∶
          a ∈ dom ((m ˢ) ∪ rhs-∪ˡ)    |> id ∶
          a ∈ dom ((m ∪ˡ m') ˢ)

      dom∪ˡ⊆∪dom : dom ((m ∪ˡ m') ˢ) ⊆ dom (m ˢ) ∪ dom (m' ˢ)
      dom∪ˡ⊆∪dom {a} a∈dom∪ with ∈-∪⁻ (proj₁ dom∪ a∈dom∪)
      ... | inj₁ a∈domm = ∈-∪⁺ (inj₁ a∈domm)
      ... | inj₂ a∈domf = a∈domf ∶
          a ∈ dom rhs-∪ˡ                        |> from ∈-map ∶
          (∃[ ab ] a ≡ proj₁ ab × ab ∈ rhs-∪ˡ)  |>′
             (λ { (ab , refl , ab∈fm') →
                 ab ∈ rhs-∪ˡ ∋ ab∈fm'           |> proj₂ ∘ from ∈-filter ∶
                 ab ∈ (m' ˢ)                    |> (λ ab∈m' → to ∈-map (ab , refl , ab∈m')) ∶
                 a ∈ dom (m' ˢ)
             }) ∶
          a ∈ dom (m' ˢ)              |> ∈-∪⁺ ∘ inj₂ ∶
          a ∈ dom (m ˢ) ∪ dom (m' ˢ)

      ∪dom⊆dom∪ˡ : dom (m ˢ) ∪ dom (m' ˢ) ⊆ dom ((m ∪ˡ m') ˢ)
      ∪dom⊆dom∪ˡ {a} a∈
        with from ∈-∪ a∈
      ... | inj₁ a∈ˡ = dom∪ˡˡ a∈ˡ
      ... | inj₂ a∈ʳ = dom∪ˡʳ a∈ʳ

      dom∪ˡ≡∪dom : dom ((m ∪ˡ m')ˢ) ≡ᵉ dom (m ˢ) ∪ dom (m' ˢ)
      dom∪ˡ≡∪dom = dom∪ˡ⊆∪dom , ∪dom⊆dom∪ˡ

      -- If `k ∈ dom m₁ ∪ dom m₂` (for m₁, m₂ maps), then `(k , v) ∈ m₁ ∪⁺ m₂` for some `v`.
      dom∪-∃∪⁺
        : {k : A} → k ∈ dom (m ˢ) ∪ dom (m' ˢ) → ∃ (λ • → (k , •) ∈ (m ∪⁺ m') ˢ)
      dom∪-∃∪⁺ k∈ = from dom∈ (∪dom⊆dom∪⁺ k∈)

      -- If `(k , v) ∈ m₁ ∪⁺ m₂`, then `k ∈ dom m₁ ∪ dom m₂`.
      ∪⁺-dom∪
        : {k : A} {v : V} → (k , v) ∈ (m ∪⁺ m') ˢ → k ∈ dom (m ˢ) ∪ dom (m' ˢ)
      ∪⁺-dom∪ {v = v} kv∈ = dom∪⁺⊆∪dom (to dom∈ (v , kv∈))

    -- The image of a key `k ∈ dom m₁ ∪ dom m₂` under the map `m₁ ∪⁺ m₂` is
    --  `fold id id _◇_ (unionThese m₁ m₂ k p)`.
    ∥_∪⁺_∥ : {k : A} (m m' : Map A V) → k ∈ dom (m ˢ) ∪ dom (m' ˢ) → V
    ∥_∪⁺_∥ {k} m₁ m₂ p = fold id id _◇_ (unionThese m₁ m₂ k p)

    -- F[ m₁ , m₂ ] takes a key `k` and a proof of `k ∈ dom m₁ ∪ dom m₂` and returns
    -- the pair `(k , v)` where `v` is the unique image of `k` under `m₁ ∪⁺ m₂`.
    -- i.e., `(k , v) ∈ m₁ ∪⁺ m₂`.
    F[_,_] : (m m' : Map A V) → ∃ (_∈ dom (m ˢ) ∪ dom (m' ˢ)) → A × V
    F[ m₁ , m₂ ] (x , x∈) = x , ∥ m₁ ∪⁺ m₂ ∥ x∈

  opaque
    filterᵐ-singleton-false
      : {P : A → Type} {k : A} {v : B} (spP : specProperty P)
      → ¬ P k → filterᵐ (sp-∘ spP proj₁) ❴ k , v ❵ᵐ ≡ᵐ ∅ᵐ
    filterᵐ-singleton-false {P = P} _ ¬p .proj₁ x =
      ⊥-elim $ ¬p $
        subst
          (P ∘ proj₁)
          (from ∈-singleton $ proj₂ (from ∈-filter x))
          (proj₁ $ from ∈-filter x)
    filterᵐ-singleton-false _ _ .proj₂ = ⊥-elim ∘ ∉-∅
      where
        open import Axiom.Set.Properties th using (∉-∅)

    add-excluded-∪ˡ-l
      : {P : A → Type} {k : A} {v : B}
        ⦃ _ : DecEq A ⦄
        (spP : specProperty P) (m : Map A B)
      → ¬ P k
      → filterᵐ (sp-∘ spP proj₁) (m ∪ˡ ❴ k , v ❵ᵐ) ≡ᵐ filterᵐ (sp-∘ spP proj₁) m
    add-excluded-∪ˡ-l {B} {k = k} {v = v} spP m ¬p with k ∈? dom (m ˢ)
    ... | yes k∈m =
        filterᵐ-cong
          {m = m ∪ˡ ❴ k , v ❵ᵐ}
          {m' = m}
          (singleton-∈-∪ˡ {m = m} k∈m)
    ... | no k∉m = begin
        filterᵐ (sp-∘ spP proj₁) (m ∪ˡ ❴ k , v ❵ᵐ) ˢ
          ≈⟨ filter-cong $ disjoint-∪ˡ-∪ (disjoint-sing k∉m) ⟩
        filter (sp-∘ spP proj₁) (m ˢ ∪ ❴ k , v ❵)
          ≈⟨ filter-hom-∪ ⟩
        filter (sp-∘ spP proj₁) (m ˢ) ∪ filter (sp-∘ spP proj₁) ❴ k , v ❵
          ≈⟨ ∪-cong ≡ᵉ.refl (filterᵐ-singleton-false spP ¬p) ⟩
        filter (sp-∘ spP proj₁) (m ˢ) ∪ ∅
          ≈⟨ ∪-identityʳ (filter (sp-∘ spP proj₁) (m ˢ)) ⟩
        filter (sp-∘ spP proj₁) (m ˢ)
        ∎
      where
        open import Axiom.Set.Properties th using
          (≡ᵉ-Setoid; ≡ᵉ-isEquivalence; ∪-cong; ∪-identityʳ; filter-cong ; filter-hom-∪)
        open import Relation.Binary.Structures using (IsEquivalence)
        module ≡ᵉ = IsEquivalence (≡ᵉ-isEquivalence {A × B})
        open import Relation.Binary.Reasoning.Setoid (≡ᵉ-Setoid{Σ A (λ x → B)})
        open import Axiom.Set.Rel th using (∈-dom-singleton-pair)

        disjoint-sing
          : k ∉ dom (m ˢ) → disjoint (dom (m ˢ)) (dom (singleton (k , v)))
        disjoint-sing k∉m a∈d a∈sing
          rewrite from ∈-dom-singleton-pair a∈sing = k∉m a∈d
