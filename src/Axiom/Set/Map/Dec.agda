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
      open Unionᵐ sp-∈ using (_∪ˡ_)

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
