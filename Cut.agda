open import Foc

open import Data.String hiding (_++_)
open import Data.List
open import Data.Unit
open import Data.Nat
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Any
open import Data.List.Any.Properties
open import Data.List.All
open Membership-≡

module Cut where

cut⁺ : ∀{A U Γ Ω}
  → suspnormalΓ Γ
  → suspnormal U
  → Value Γ A
  → Term Γ (A ∷ Ω) U
  → Term Γ Ω U

cut⁻ : ∀{U Γ A}
  → suspnormalΓ Γ
  → suspstable U
  → (LA : List (Type ⁻))
  → Term Γ [] (Inv A)
  → Spine Γ (A ∷ LA) [] U
  → Spine Γ LA [] U

rsubst : ∀{Γ Form} (Γ' : Ctx)
  → suspnormalΓ (Γ' ++ Γ)
  → suspnormalF Form
  → (LA : (List (Type ⁻)))
  → All (\x → Term (Γ' ++ Γ) [] (Inv x)) LA
  → Exp (Γ' ++ (Data.List.map (Pers) LA) ++ Γ) Form
  → Exp (Γ' ++ Γ) Form

lsubst : ∀{Γ U L A}
  → suspnormalΓ Γ
  → suspstable U
  → Exp Γ (Left L (True A))
  → Term Γ [ A ] U
  → Exp Γ (Left L U)

-- Positive principal substitution

cut⁺ pfΓ pf (id⁺ x) N with pfΓ x
cut⁺ pfΓ pf (id⁺ x) (η⁺ N) | _ , refl = subst⁺ [] (id⁺ x) N
cut⁺ pfΓ pf (id⁺ x) (↑L-nil Y Z)  | _ , refl = cut⁺ pfΓ pf (id⁺ x) Z
cut⁺ pfΓ pf (↓R M) (↓L N) = {!!} -- rsubst [] pfΓ pf ? ?
cut⁺ pfΓ pf (∨R₁ V) (∨L N₁ N₂) = cut⁺ pfΓ pf V N₁
cut⁺ pfΓ pf (∨R₂ V) (∨L N₁ N₂) = cut⁺ pfΓ pf V N₂
cut⁺ pfΓ pf ⊤⁺R (⊤⁺L N) = N
cut⁺ pfΓ pf (∧⁺R V₁ V₂) (∧⁺L N) = cut⁺ pfΓ pf V₂ (cut⁺ pfΓ pf V₁ N)
cut⁺ pfΓ pf V (↑L-nil _ Z) = cut⁺ pfΓ pf V Z

-- Negative principle substitution
cut⁻ = {!!}
{- cut⁻ pfΓ pf (focL () x Sp') Sp
cut⁻ pfΓ pf (η⁻ N) id⁻ = N
cut⁻ pfΓ (_ , ()) N (id⁻ {↑ A})
cut⁻ pfΓ (_ , ()) N (id⁻ {A ⊃ B})
cut⁻ pfΓ (_ , ()) N (id⁻ {⊤⁻})
cut⁻ pfΓ (_ , ()) N (id⁻ {A ∧⁻ B})
cut⁻ pfΓ pf (↑R N) (↑L _ M) = lsubst pfΓ pf N M
cut⁻ pfΓ pf (⊃R N) (⊃L V Sp) = cut⁻ pfΓ pf (cut⁺ pfΓ tt V N) Sp
cut⁻ pfΓ pf (∧⁻R N₁ N₂) (∧⁻L₁ Sp) = cut⁻ pfΓ pf N₁ Sp
cut⁻ pfΓ pf (∧⁻R N₁ N₂) (∧⁻L₂ Sp) = cut⁻ pfΓ pf N₂ Sp -}

postulate 
  subseteq-in : ∀{L Γ' Γ A} → Data.List.map Pers L ⊆ (Γ' ++ Pers A ∷ Γ) → A ∈ L ⊎ A ∉ L

postulate 
  subseteq-notin : ∀{L Γ' Γ A} → Data.List.map Pers L ⊆ Γ' ++ Pers A ∷ Γ → A ∉ L → Data.List.map Pers L ⊆ Γ' ++ Γ



-- Substitution into values
rsubst Γ' pfΓ pf LA M (id⁺ z) with fromctxGen Γ' (Data.List.map Pers LA) z
rsubst Γ' pfΓ pf LA M (id⁺ z) | inj₁ x = ⊥-elim (no-hsusp-in-pers LA x)
rsubst Γ' pfΓ pf LA M (id⁺ z) | inj₂ y = id⁺ y
rsubst Γ' pfΓ pf LA M (↓R N) = ↓R (rsubst Γ' pfΓ pf LA M N)
rsubst Γ' pfΓ pf LA M (∨R₁ V) = ∨R₁ (rsubst Γ' pfΓ pf LA M V)
rsubst Γ' pfΓ pf LA M (∨R₂ V) = ∨R₂ (rsubst Γ' pfΓ pf LA M V)
rsubst Γ' pfΓ pf LA M ⊤⁺R = ⊤⁺R
rsubst Γ' pfΓ pf LA M (∧⁺R V₁ V₂) =
  ∧⁺R (rsubst Γ' pfΓ pf LA M V₁) (rsubst Γ' pfΓ pf LA M V₂)

-- Substitution into terms
rsubst Γ' pfΓ pf LA M (focR V) = focR (rsubst Γ' pfΓ pf LA M V)
rsubst Γ' pfΓ pf LA M (focL {L} pf' x' Sp) = {!!}
--... | inj₁ x = cut⁻ pfΓ (pf' , pf) L {!!} (rsubst Γ' pfΓ pf LA M Sp)
--... | inj₂ y = focL pf' (subseteq-notin {L} {Γ'} x' y) (rsubst Γ' pfΓ pf LA M  Sp)
--rsubst Γ' pfΓ pf LA M (focL pf' x' Sp) with fromctx Γ' x'
--... | inj₁ refl = cut⁻ pfΓ (pf' , pf) M (rsubst Γ' pfΓ pf LA M Sp)
--... | inj₂ x = focL pf' x (rsubst Γ' pfΓ pf LA M Sp)
rsubst Γ' pfΓ pf LA M (η⁺ N) = {!!} --η⁺ (rsubst (_ ∷ Γ') (conssusp pfΓ) pf LA (wken M) N)
rsubst Γ' pfΓ pf LA M (↓L N) = {!!} --↓L (rsubst (_ ∷ Γ') (conspers pfΓ) pf LA (wken M) N)
rsubst Γ' pfΓ pf LA M ⊥L = ⊥L
rsubst Γ' pfΓ pf LA M (∨L N₁ N₂) =
  ∨L (rsubst Γ' pfΓ pf LA M N₁) (rsubst Γ' pfΓ pf LA M N₂)
rsubst Γ' pfΓ pf LA M (⊤⁺L N) = ⊤⁺L (rsubst Γ' pfΓ pf LA M N)
rsubst Γ' pfΓ pf LA M (∧⁺L N) = ∧⁺L (rsubst Γ' pfΓ pf LA M N)
rsubst Γ' pfΓ pf LA M (η⁻ N) = η⁻ (rsubst Γ' pfΓ pf LA M N)
rsubst Γ' pfΓ pf LA M (↑R N) = ↑R (rsubst Γ' pfΓ pf LA M N)
rsubst Γ' pfΓ pf LA M (⊃R N) = ⊃R (rsubst Γ' pfΓ pf LA M N)
rsubst Γ' pfΓ pf LA M ⊤⁻R = ⊤⁻R
rsubst Γ' pfΓ pf LA M (∧⁻R N₁ N₂) =
  ∧⁻R (rsubst Γ' pfΓ pf LA M N₁) (rsubst Γ' pfΓ pf LA M N₂)

-- Substitution into spines
rsubst Γ' pfΓ pf LA M id⁻ = id⁻
rsubst Γ' pfΓ pf LA M (↑L-cons pf' N) = ↑L-cons pf' (rsubst Γ' pfΓ pf LA M N)
rsubst Γ' pfΓ pf LA M (↑L-nil pf' N) = ↑L-nil pf' (rsubst Γ' pfΓ pf LA M N)

rsubst Γ' pfΓ pf LA M (⊃L V Sp) =
  ⊃L (rsubst Γ' pfΓ tt LA M V) (rsubst Γ' pfΓ pf LA M Sp)
rsubst Γ' pfΓ pf LA M (∧⁻L₁ Sp) = ∧⁻L₁ (rsubst Γ' pfΓ pf LA M Sp)
rsubst Γ' pfΓ pf LA M (∧⁻L₂ Sp) = ∧⁻L₂ (rsubst Γ' pfΓ pf LA M Sp)

-- Substitution out of terms
lsubst pfΓ pf (focR V) N = cut⁺ pfΓ (proj₂ pf) V N
lsubst pfΓ pf (focL pf' x Sp) N = focL (proj₁ pf) x (lsubst pfΓ pf Sp N)
lsubst pfΓ pf (η⁺ M) N = η⁺ (lsubst (conssusp pfΓ) pf M (wken N))
lsubst pfΓ pf (↓L M) N = ↓L (lsubst (conspers pfΓ) pf M (wken N))
lsubst pfΓ pf ⊥L M = ⊥L
lsubst pfΓ pf (∨L M₁ M₂) N = ∨L (lsubst pfΓ pf M₁ N) (lsubst pfΓ pf M₂ N)
lsubst pfΓ pf (⊤⁺L M) N = ⊤⁺L (lsubst pfΓ pf M N)
lsubst pfΓ pf (∧⁺L M) N = ∧⁺L (lsubst pfΓ pf M N)

-- Substitution of of spines
lsubst pfΓ pf (↑L-cons _ M) N = ↑L-cons (proj₁ pf) (lsubst pfΓ pf M N)
lsubst pfΓ pf (↑L-nil _ M) N = ↑L-nil (proj₁ pf) (lsubst pfΓ pf M N)

lsubst pfΓ pf (⊃L V Sp) N = ⊃L V (lsubst pfΓ pf Sp N)
lsubst pfΓ pf (∧⁻L₁ Sp) N = ∧⁻L₁ (lsubst pfΓ pf Sp N)
lsubst pfΓ pf (∧⁻L₂ Sp) N = ∧⁻L₂ (lsubst pfΓ pf Sp N)
