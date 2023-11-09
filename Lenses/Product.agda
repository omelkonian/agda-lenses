module Lenses.Product where

open import Level using (Level)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Lenses.Core

private variable ℓ : Level; A B : Set ℓ

lens-×ˡ : Lens (A × B) A
lens-×ˡ = λ where
  .get → proj₁
  .set (a , b) a′ → (a′ , b)

lens-×ʳ : Lens (A × B) B
lens-×ʳ = λ where
  .get → proj₂
  .set (a , b) b′ → (a , b′)
