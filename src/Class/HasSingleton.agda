{-# OPTIONS --safe #-}

open import Axiom.Set using (Theory)

module Class.HasSingleton {ℓ} {ℓ_c} (th : Theory {ℓ} {ℓ_c}) where

open Theory th renaming (Set to ℙ_; ❴_❵ to ❴_❵ˢ)

open import Axiom.Set.Map th
open import abstract-set-theory.Prelude

private variable A B : Type ℓ

record HasSingleton (A B : Type ℓ) : Type ℓ where
  field
    ❴_❵ : A → B

open HasSingleton ⦃...⦄ public

instance
  HasSingletonSet-Set : ⦃ _ : Cs A ⦄ → HasSingleton A (ℙ A)
  HasSingletonSet-Set = record { ❴_❵ = ❴_❵ˢ }

  HasSingletonSet-Map : ⦃ _ : Cs A ⦄ → ⦃ _ : Cs B ⦄ → HasSingleton (A × B) (Map A B)
  HasSingletonSet-Map = record { ❴_❵ = ❴_❵ᵐ }
