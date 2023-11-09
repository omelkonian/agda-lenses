module Lenses.Identity {ℓ} {A : Set ℓ} where

open import Function using (id)

open import Lenses.Core

lens-id : Lens A A
lens-id = λ where
  .get → id
  .set → λ _ → id
