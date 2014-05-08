open import Data.List
open import Data.List.Any
open Membership-≡

open import Foc


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

cntr-term : ∀{Γ X L+ U} → Term Γ (X ∷ L+) U → HSusp X ∈ Γ → Term Γ L+ U

cntr-term {X = a Q .⁺} (η⁺ N) In = {!!}
cntr-term {X = ↓ X} T In = {!!}
cntr-term {X = ⊥⁺} (⊥L ) In = {!!}
cntr-term {X = X ∨ X₁} T In = {!!}
cntr-term {X = ⊤⁺} T In = {!!}
cntr-term {X = X ∧⁺ X₁} T In = {!!}

cntr-+-[]-spine-bis (a Q .⁺) (↑L-nil pf N) In = {!!}
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


cntr-+-[]-spine {L+ = []} X (↑L-nil pf N) In = {!!}
cntr-+-[]-spine {L+ = x ∷ L+} X Sp In = {!!}

{- cntr-+-[]-spine-absurd : ∀{Γ L+ U} 
  → (X : Type ⁺) 
  → Spine Γ [] (L+ ++ [ X ]) U 
  → Pers (↑ X) ∈ Γ
  →  Spine Γ [] L+ U
-}