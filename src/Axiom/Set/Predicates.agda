{-# OPTIONS --type-in-type --no-import-sorts #-}

module Axiom.Set.Predicates where

open import abstract-set-theory.Prelude

open import Axiom.Set

import Relation.Unary as P
import Function.Properties.Equivalence as E

Pred-Model : Theory
Pred-Model = λ where
  .Set           → λ A → A → Type
  ._∈_           → λ x X → X x
  .sp            → ⊤-SpecProperty
  .specification {_} {P} → λ X _ → P P.∩ X , E.refl
  .unions        → λ X → (λ a → ∃[ Z ] X Z × Z a) , E.refl
  .replacement   → λ f X → (λ b → ∃[ a ] b ≡ f a × X a) , E.refl
  .listing       → λ l → (_∈ˡ l) , E.refl
    where open Theory
