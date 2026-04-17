{-# OPTIONS --safe --no-import-sorts #-}

open import Axiom.Set using (Theory)

module Class.HasEmptySet {ℓ} {ℓ_c} (th : Theory {ℓ} {ℓ_c}) where

open import abstract-set-theory.Prelude

open Theory th renaming (∅ to ∅ˢ)
open import Axiom.Set.Map th

private variable A B : Type ℓ

record HasEmptySet (A : Type ℓ) : Type ℓ where
  field
    ∅ : A

open HasEmptySet ⦃...⦄ public

instance
  HasEmptySet-Set : ⦃ _ : Cs A ⦄ → HasEmptySet (Set A)
  HasEmptySet-Set = record { ∅ = ∅ˢ }

  HasEmptySet-Map : ⦃ _ : Cs A ⦄ → ⦃ _ : Cs B ⦄ → HasEmptySet (Map A B)
  HasEmptySet-Map = record { ∅ = ∅ᵐ }
