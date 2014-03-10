open import Foc
open import Cut

open import Data.List
open import Data.Product
open import Data.Sum
open import Data.List.All
open import Data.List.Any
open import Data.List.Any.Properties
open import Data.Unit
open import Data.Nat
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])

module MulticutBasedOn where

mcut⁺ : ∀{U Γ Ω}
  → suspnormalΓ Γ
  → suspnormal U
  → (LAi : List (Type ⁺))
  → All (\x → Value Γ x) LAi
  → Term Γ (LAi ++ Ω) U
  → Term Γ Ω U

mcut⁺ pfΓ pf [] [] T = T
mcut⁺ pfΓ pf (x ∷ LA) (px ∷ VAs) T = mcut⁺ pfΓ pf LA VAs (cut⁺ pfΓ pf px T) 


mcut⁻ : ∀{U Γ N} 
  → suspnormalΓ Γ 
  → suspstable U
  → (LA : List (Type ⁻))
  → (length LA ≡ suc N)
  → All (\x → Term Γ [] (Inv x)) LA
  → All (\x → Spine Γ x U) LA
  → Term Γ [] U

mcut⁻ pfΓ pf [] () Ts Sps
mcut⁻ pfΓ pf (x ∷ LA) _ (y ∷ _) (z ∷ _) = cut⁻ pfΓ pf y z

mrsubst  : ∀{Γ Form} (Γ' : Ctx)
  → suspnormalΓ (Γ' ++ Γ)
  → suspnormalF Form
  → (LA- : List (Type ⁻))
  → All (\x →  Term (Γ' ++ Γ) [] (Inv x)) LA-
  → Exp (Γ' ++ (Data.List.map (\x → Pers x) LA-) ++ Γ) Form
  → Exp (Γ' ++ Γ) Form



mrsubst Γ' pfΓ pf [] Ts Exp = Exp
mrsubst {Γ} Γ' pfΓ pf (x ∷ LA) (px ∷ Ts) Exp = 
  mrsubst Γ' pfΓ pf LA Ts 
    (rsubst  { Data.List.map Pers LA ++ Γ} Γ' (concconcpers Γ' LA pfΓ) pf {!!} Exp)

  {-
--rsubst : ∀{Γ Form A} (Γ' : Ctx)
--  → suspnormalΓ (Γ' ++ Γ)
--  → suspnormalF Form
--  → Term (Γ' ++ Γ) [] (Inv A)
--  → Exp (Γ' ++ (Pers A) ∷ Γ) Form
--  → Exp (Γ' ++ Γ) Form 

lsubst : ∀{Γ U L A} 
  → suspnormalΓ Γ
  → suspstable U
  → Exp Γ (Left L (True A))
  → Term Γ [ A ] U 
  → Exp Γ (Left L U)


-}
