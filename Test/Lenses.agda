-- {-# OPTIONS -v derive-lenses:100 #-}
module Test.Lenses where

open import Function using (_∋_)
open import Data.Nat using (ℕ; _∸_)
open import Data.Product using (_,_)
open import Data.String using (String; _++_)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Lenses

record R₀ : Set where
  field
    x : ℕ
    y : String
open R₀
unquoteDecl 𝕩 _∙x _∙x=_ _∙x↝_
            𝕪 _∙y _∙y=_ _∙y↝_
  = deriveLenses (quote R₀)
    ( (𝕩 , _∙x , _∙x=_ , _∙x↝_)
    ∷ (𝕪 , _∙y , _∙y=_ , _∙y↝_)
    ∷ [])
infixl 10 _∙x=_ _∙x↝_ _∙y=_ _∙y↝_

ex-record : R₀
ex-record = record {x = 42; y = "test"}

_ = ex-record ∙y ≡ "test"
  ∋ refl

_ = (ex-record ∙y= "TEST") ∙y ≡ "TEST"
  ∋ refl

_ = (ex-record ∙x= 422) ∙x ≡ 422
  ∋ refl

_ = ex-record ∙y= "TEST"
              ∙x= 422
  ≡ record {x = 422; y = "TEST"}
  ∋ refl

_ = ex-record ∙y↝ ("$" ++_)
              ∙x= 422
              ∙x↝ (_∸ 1)
  ≡ record {x = 421; y = "$test"}
  ∋ refl
