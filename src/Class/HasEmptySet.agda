{-# OPTIONS --safe --no-import-sorts #-}

open import Axiom.Set using (Theory)

module Class.HasEmptySet (th : Theory) where

open import abstract-set-theory.Prelude

open Theory th renaming (∅ to ∅ˢ)
open import Axiom.Set.Map th

record HasEmptySet (A : Type) : Type where
  field
    ∅ : A

open HasEmptySet ⦃...⦄ public

instance
  HasEmptySet-Set : {A : Type} → HasEmptySet (Set A)
  HasEmptySet-Set = record { ∅ = ∅ˢ }

  HasEmptySet-Map : {A B : Type} → HasEmptySet (Map A B)
  HasEmptySet-Map = record { ∅ = ∅ᵐ }
