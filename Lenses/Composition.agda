module Lenses.Composition where

open import Level using (Level)
open import Function using (id; _∘_)

open import Lenses.Core

private variable ℓ : Level; A B C : Set ℓ

_lens-∘_ : Lens A B → Lens B C → Lens A C
A⟫B lens-∘ B⟫C = λ where
    .get → _∙c ∘ _∙b
    .set a c → a ∙b↝ (_∙c= c)
  where open Lens A⟫B renaming (get to _∙b; set to _∙b=_; modify to _∙b↝_)
        open Lens B⟫C renaming (get to _∙c; set to _∙c=_)
