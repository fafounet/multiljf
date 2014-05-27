open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open import Data.List
open import Data.List.Any
open import Data.Empty
open Membership-≡
open import Data.Sum
open import Data.Product


open import Foc
open import FocWeak
open import FocSimpleProps

module FocCntr where



postulate
  value-term-∧⁺R-absurd :  ∀{Q R} 
    → Q ≢ R
    → Value [ HSusp (a Q ⁺) ] (a Q ⁺) 
    → Term [ HSusp (a Q ⁺) ]  [] (True (a R ⁺)) 
    → Term [ HSusp (a Q ⁺) ] [] (True ((a Q ⁺) ∧⁺ (a R ⁺)))
    → ⊥
{-value-term-∧⁺R-absurd Ieq (id⁺ v) (focR (id⁺ v₁)) (focR (id⁺ (here ())))
value-term-∧⁺R-absurd Ieq (id⁺ v) (focR (id⁺ v₁)) (focR (id⁺ (there ())))
value-term-∧⁺R-absurd Ieq (id⁺ v) (focR (id⁺ v₁)) (focR (∧⁺R V₁ (id⁺ (here refl)))) = Ieq refl
value-term-∧⁺R-absurd Ieq (id⁺ v) (focR (id⁺ v₁)) (focR (∧⁺R V₁ (id⁺ (there ()))))
value-term-∧⁺R-absurd Ieq (id⁺ v) (focR (id⁺ (here refl))) (focL-init pf Sp) = Ieq refl
value-term-∧⁺R-absurd Ieq (id⁺ v) (focR (id⁺ (there ()))) (focL-init pf Sp)
--
value-term-∧⁺R-absurd Ieq (id⁺ v) (focL-init pf Sp) (focR (id⁺ (here ())))
value-term-∧⁺R-absurd Ieq (id⁺ v) (focL-init pf Sp) (focR (id⁺ (there ())))
value-term-∧⁺R-absurd Ieq (id⁺ v) (focL-init pf Sp) (focR (∧⁺R V₁ (id⁺ (here refl)))) = Ieq refl
value-term-∧⁺R-absurd Ieq (id⁺ v) (focL-init pf Sp) (focR (∧⁺R V₁ (id⁺ (there ()))))
--
value-term-∧⁺R-absurd Ieq (id⁺ v) (focL-init pf Sp) (focL-init pf₁ Sp₁) = {!!}
-}

{- Something like this is not true:
value-true-context : ∀{Γ A} → Value Γ A → (HSusp A  ∈ Γ) ⊎ (Pers (↑ A) ∈ Γ) ⊎ (A ≡ ⊤⁺)
term-true-context : ∀{Γ A} → Term Γ [] (True A) →  (HSusp A  ∈ Γ) ⊎ (Pers (↑ A) ∈ Γ) ⊎ (A ≡ ⊤⁺)
-}



cntr-pers-term : ∀{Γ L+ X U} → stable U → Term Γ (L+ ++ [ X ]) U → Pers (↑ X) ∈ Γ → Term Γ L+ U

cntr-pers-term {L+ = []} pf T In = 
  focL-init pf (focL-step pf In (focL-end pf (↑L-cons pf (↑L-nil pf T))))
cntr-pers-term {L+ = a Q .⁺ ∷ L+} pf (η⁺ N) In = η⁺ (cntr-pers-term pf N (there In))
cntr-pers-term {L+ = ↓ A ∷ L+} pf (↓L N) In = ↓L (cntr-pers-term pf N (there In))
cntr-pers-term {L+ = ⊥⁺ ∷ L+} pf T In = ⊥L
cntr-pers-term {L+ = A ∨ B ∷ L+} pf (∨L N₁ N₂) In = 
  ∨L (cntr-pers-term pf N₁ In) (cntr-pers-term pf N₂ In)
cntr-pers-term {L+ = ⊤⁺ ∷ L+} pf (⊤⁺L N) In = 
  ⊤⁺L (cntr-pers-term pf N In)
cntr-pers-term {L+ = Z ∧⁺ Z₁ ∷ L+} pf (∧⁺L N) In = ∧⁺L (cntr-pers-term pf N In) 




cntr-+-[]-spine : ∀{Γ Y L+ U}
  → stable U 
  → (X : Type ⁺) 
  → Spine Γ [] ((Y ∷ L+) ++ [ X ]) U 
  → Pers (↑ X) ∈ Γ
  → Spine Γ [] (Y ∷ L+) U

cntr-+-[]-spine pf X (↑L-nil pf₁ N) In = ↑L-nil pf₁ (cntr-pers-term pf₁ N In)



-- The following is not true:
-- cntr-hsusp-term : ∀{Γ X L+ U} → Term Γ (X ∷ L+) U → HSusp X ∈ Γ → Term Γ L+ U
-- due to the following:
cntr-term-absurd : ∀{Q} → Term [ HSusp (⊥⁺) ]  [ ⊥⁺ ]  (Susp (a Q ⁻)) → Term [ HSusp (⊥⁺) ]  []  (Susp (a Q ⁻)) → ⊥
cntr-term-absurd ⊥L (focL-init pf (focL-step pf₁ (here ()) Sp))
cntr-term-absurd ⊥L (focL-init pf (focL-step pf₁ (there ()) Sp))
cntr-term-absurd ⊥L (focL-init pf (focL-end pf₁ ()))