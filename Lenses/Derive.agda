-- {-# OPTIONS -v derive-lenses:100 #-}
module Lenses.Derive where

open import Function using (_$_)
open import Data.Unit using (⊤)
open import Data.List using (List; zip; _∷_; []; [_])
open import Data.Product using (_,_; _×_)
open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Reflection hiding (_>>=_; _>>_)
open import Reflection.AST.Meta

open import Reflection.Utils.Debug
open import Reflection.Syntax
open import Reflection.Utils
open Debug ("derive-lenses" , 100)

open import Class.Show
open import Class.Semigroup
open import Class.Monad

open import Lenses.Core

deriveLenses : Name → List (Name × Name × Name × Name) → TC ⊤
deriveLenses n lns = do
  print "**************************"
  print $ "Deriving lenses for " ◇ show n
  d@(record-type _ fs) ← getDefinition n
    where _ → error "Not a record type"
  print $ "fields: " ◇ show fs
  let fs = vArgs fs
  return⊤ $ forM (zip fs lns) $ λ where (f , (ln , gn , sn , mn)) → do
    (pi _ (abs _ fTy)) ← getType f
      where _ → error "Not a field type (should be `<RECORD> → <FIELD>`)."
    genSimpleDef ln (quote Lens ∙⟦ n ∙ ∣ fTy ⟧) $
     mkRecord ( (quote Lens.get , f ∙)
              ∷ (quote Lens.set , `λ⟦ "r" ∣ "x′" ⇒ updateField fs (♯ 1) f (♯ 0) ⟧)
              ∷ [])
    genSimpleDef gn (quote Getter ∙⟦ n ∙ ∣ fTy ⟧) $
      quote Lens.get ∙⟦ ln ∙ ⟧
    genSimpleDef sn (quote Setter ∙⟦ n ∙ ∣ fTy ⟧) $
      quote Lens.set ∙⟦ ln ∙ ⟧
    genSimpleDef mn (quote Modifier ∙⟦ n ∙ ∣ fTy ⟧) $
      quote Lens.modify ∙⟦ ln ∙ ⟧
