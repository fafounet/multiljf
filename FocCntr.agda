open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open import Data.List
open import Data.List.Any
open import Data.Empty
open Membership-≡
open import Data.Sum
open import Data.Product


open import Foc
open import Weak
open import FocSimpleProps
open import Identity

module FocCntr where


cntr---sing-spine : ∀{Γ X Y L U} 
  → (L' : List (Type ⁻)) 
  → Spine Γ (Y ∷ L) [ X ] U
  → Pers (↑ X) ∈ Γ 
  → Spine Γ (Y ∷ L) [] U 

cntr---[]-spine : ∀{Γ X L A U} 
  → (L' : List (Type ⁻)) 
  → Spine Γ (A ∷ (X ∷ L)) [] U
  → Pers A ∈ Γ 
  → Spine Γ (X ∷ L) [] U 

cntr-+-[]-spine : ∀{Γ Y L+ U} 
  → (X : Type ⁺) 
  → Spine Γ [] ((Y ∷ L+) ++ [ X ]) U 
  → Pers (↑ X) ∈ Γ
  →  Spine Γ [] (Y ∷ L+) U

cntr-+-[]-spine-bis : ∀{Γ Y L+ U} 
  → (X : Type ⁺) 
  → Spine Γ [] (X ∷ Y ∷ L+) U 
  → Pers (↑ X) ∈ Γ
  → Spine Γ [] (Y ∷ L+) U


value-term-∧⁺R-absurd :  ∀{Q R} 
  → Q ≢ R
  → Value [ HSusp (a Q ⁺) ] (a Q ⁺) 
  → Term [ HSusp (a Q ⁺) ]  [] (True (a R ⁺)) 
  → Term [ HSusp (a Q ⁺) ] [] (True ((a Q ⁺) ∧⁺ (a R ⁺)))
  → ⊥
value-term-∧⁺R-absurd Ieq V T1 T2 = {!!}

{- Something like this is not true:
value-true-context : ∀{Γ A} → Value Γ A → (HSusp A  ∈ Γ) ⊎ (Pers (↑ A) ∈ Γ) ⊎ (A ≡ ⊤⁺)
term-true-context : ∀{Γ A} → Term Γ [] (True A) →  (HSusp A  ∈ Γ) ⊎ (Pers (↑ A) ∈ Γ) ⊎ (A ≡ ⊤⁺)

-}


--term-spine-∧⁺R-adm :  ∀{Γ A B} → Term Γ [] (True A) → Term Γ [ (True B) → Term Γ [] (True (A ∧⁺ B))
value-term-∧⁺R-adm :  ∀{Γ A B} → Value Γ A → Term Γ [] (True B) → Term Γ [] (True (A ∧⁺ B))
value-term-∧⁺R-adm V (focR V₁) = focR (∧⁺R V V₁)
value-term-∧⁺R-adm V (focL-init pf (focL-step pf₁ In (focL-step pf₂ In₁ Sp))) = {!!}
value-term-∧⁺R-adm V (focL-init pf (focL-step pf₁ In (focL-end pf₂ Sp))) = {!!}
value-term-∧⁺R-adm V (focL-init pf (focL-end pf₁ ()))

term-∧⁺R-adm : ∀{Γ A B} → Term Γ [] (True A) → Term Γ [] (True B) → Term Γ [] (True (A ∧⁺ B))
term-∧⁺R-adm (focR V) T = {!!} -- Imposible
term-∧⁺R-adm (focL-init pf Sp) (focR V) = {!!}
term-∧⁺R-adm (focL-init pf Sp) (focL-init pf₁ Sp₁) = {!!} 

aaa : ∀{Γ A Q} → Value Γ A → Pers (↑ (a Q ⁺)) ∈ Γ →  Term (HSusp (a Q ⁺) ∷ Γ) [] (True A)
aaa (id⁺ v) In = focR (id⁺ (there v))
aaa (↓R N) In = {!!}
aaa (∨R₁ V) In = {!!}
aaa (∨R₂ V) In = {!!}
aaa ⊤⁺R In = {!!}
aaa (∧⁺R V₁ V₂) In = {!(aaa V₁ In)!}

hmmm : ∀{Γ Q L+ U} → Term Γ L+ U → Pers (↑ (a Q ⁺)) ∈ Γ → Term (HSusp (a Q ⁺) ∷ Γ) L+ U
hmmm (focR V) In = {!!}
hmmm (focL-init pf Sp) In = {!!}
hmmm (η⁺ N) In = {!!}
hmmm (↓L N) In = {!!}
hmmm ⊥L In = ⊥L
hmmm (∨L N₁ N₂) In = ∨L (hmmm N₁ In) (hmmm N₂ In)
hmmm (⊤⁺L N) In = ⊤⁺L (hmmm N In)
hmmm (∧⁺L N) In = ∧⁺L (hmmm N In)
hmmm (η⁻ N) In = η⁻ (hmmm N In)
hmmm (↑R N) In = ↑R (hmmm N In)
hmmm (⊃R N) In = ⊃R (hmmm N In)
hmmm ⊤⁻R In = ⊤⁻R
hmmm (∧⁻R N₁ N₂) In = ∧⁻R (hmmm N₁ In) (hmmm N₂ In)

tps : ∀{Γ Q Y L+ U} → Term Γ (a Q ⁺ ∷ Y ∷ L+) U → Pers (↑ (a Q ⁺)) ∈ Γ → Spine Γ [] (Y ∷ L+) U
tps (η⁺ N) In = {!!}

cntr-+-[]-spine-bis (a Q .⁺) (↑L-nil pf N) In = tps N In
cntr-+-[]-spine-bis (↓ X) Sp In = {!!}
cntr-+-[]-spine-bis ⊥⁺ Sp In = {!!}
cntr-+-[]-spine-bis (X ∨ X₁) Sp In = {!!}
cntr-+-[]-spine-bis ⊤⁺ Sp In = {!!}
cntr-+-[]-spine-bis (X ∧⁺ X₁) Sp In = {!!}

cntr---sing-spine L' (↑L-cons {Z} pf N) In = {!!}
cntr---sing-spine L' (⊃L V Sp) In = ⊃L V (cntr---sing-spine L' Sp In)
cntr---sing-spine L' (∧⁻L₁ Sp) In = ∧⁻L₁ (cntr---sing-spine L' Sp In)
cntr---sing-spine L' (∧⁻L₂ Sp) In = ∧⁻L₂ (cntr---sing-spine L' Sp In)



cntr---[]-spine {A = a Q .⁻} L' Sp In = {!⊥-elim (init-not-empty Sp)!}
cntr---[]-spine {A = ↑ y} L' (↑L-cons pf N) In = {!!}
cntr---[]-spine {A = A ⊃ A₁} L' Sp In = {!!}
cntr---[]-spine {A = ⊤⁻} L' Sp In = {!!}
cntr---[]-spine {A = A ∧⁻ A₁} L' Sp In = {!!}

postulate
  cntr-term-simpl : ∀{Γ Y  U} 
    → (X : Type ⁺) 
    → Term Γ (Y ∷ X ∷ []) U 
    → Pers (↑ X) ∈ Γ
    → Term Γ (Y ∷ []) U


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


{-
cntr-+-[]-spine : ∀{Γ Y L+ U} 
  → (X : Type ⁺) 
  → Spine Γ [] ((Y ∷ L+) ++ [ X ]) U 
  → Pers (↑ X) ∈ Γ
  →  Spine Γ [] (Y ∷ L+) U
-}
cntr-+-[]-spine {L+ = []} X (↑L-nil pf N) In = ↑L-nil pf (cntr-term-simpl X N In)
cntr-+-[]-spine {Y = a Q .⁺} {x ∷ L+} X Sp In = {!!}
cntr-+-[]-spine {Y = ↓ Y} {x ∷ L+} X Sp In = {!!}
cntr-+-[]-spine {Y = ⊥⁺} {x ∷ L+} X Sp In = {!!}
cntr-+-[]-spine {Y = Y ∨ Y₁} {x ∷ L+} X Sp In = {!!}
cntr-+-[]-spine {Y = ⊤⁺} {x ∷ L+} X Sp In = {!!}
cntr-+-[]-spine {Y = Y ∧⁺ Y₁} {x ∷ L+} X (↑L-nil pf Z) In = {!!}





{- cntr-+-[]-spine-absurd : ∀{Γ L+ U} 
  → (X : Type ⁺) 
  → Spine Γ [] (L+ ++ [ X ]) U 
  → Pers (↑ X) ∈ Γ
  →  Spine Γ [] L+ U
-}



-- The following is not true:
-- cntr-hsusp-term : ∀{Γ X L+ U} → Term Γ (X ∷ L+) U → HSusp X ∈ Γ → Term Γ L+ U
-- due to the following:
cntr-term-absurd : ∀{Q} → Term [ HSusp (⊥⁺) ]  [ ⊥⁺ ]  (Susp (a Q ⁻)) → Term [ HSusp (⊥⁺) ]  []  (Susp (a Q ⁻)) → ⊥
cntr-term-absurd ⊥L (focL-init pf (focL-step pf₁ (here ()) Sp))
cntr-term-absurd ⊥L (focL-init pf (focL-step pf₁ (there ()) Sp))
cntr-term-absurd ⊥L (focL-init pf (focL-end pf₁ ()))