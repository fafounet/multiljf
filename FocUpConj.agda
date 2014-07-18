open import Data.Nat
open import Data.List
open import Data.List.Any
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open Membership-≡

open import ListExtra

open import Foc
open import FocAdmissible


module FocUpConj where


{-
ALL THOSE LEMMAS ARE WRONG
C.F. ahmm at the end of this file
unless U is suspnormal !

value-∧⁺-context : ∀{Γ' Γ A B U} 
  → Value (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) U 
  → Value (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) U 

term-∧⁺-context : ∀{Γ' Γ A B L U} 
  → Term  (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) L U 
  → Term (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) L U 

spine-l-∧⁺-context : ∀{Γ' Γ L- A B U} 
  → Spine-l  (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) L- U 
  → Spine-l (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) L- U 

spine-∧⁺-context : ∀{Γ' Γ L- L+ A B U} 
  → Spine  (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) L- L+ U 
  → Spine (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) L- L+ U 
-}


-- It is possible to remove a delayed positive conjunction if its
-- two (shifted) components are already in the context
spine-↑∧⁺-+ : ∀{Γ A B L L1 L2 U N}  
           (Len : length L1 + length L2 + length L ≡ suc N)
           (pf : stable U) 
           (S : suspnormal U)
           (InA : Pers (↑ A) ∈ Γ) 
           (InB : Pers (↑ B) ∈ Γ) 
           (Sp : Spine Γ L (L1 ++ (A ∧⁺ B) ∷ L2)  U) 
           → Spine Γ L (L1 ++ L2) U
spine-↑∧⁺-+ {L = []} {[]} {[]} Len pf S InA InB (↑L-nil pf₁ (∧⁺L N)) = {!!}
spine-↑∧⁺-+ {L = []} {[]} {x ∷ L2} Len pf S InA InB (↑L-nil pf₁ (∧⁺L N)) = {!!}
spine-↑∧⁺-+ {L = []} {x ∷ L1} Len pf S InA InB Sp = {!!}
spine-↑∧⁺-+ {L = x ∷ L} Len pf S InA InB Sp = {!!}


-- It is possible to remove a loaded shifted positive conjunction if its
-- two (shifted) components are already in the context
spine-↑∧⁺ : ∀{Γ A B L1 L2 L+ U N}  
                (Len : length L1 + length L2 + length L+ ≡ suc N)
                (pf : stable U) 
                (S : suspnormal U)
                (InA : Pers (↑ A) ∈ Γ) 
                (InB : Pers (↑ B) ∈ Γ) 
                (Sp : Spine Γ (L1 ++ ↑ (A ∧⁺ B) ∷ L2) L+ U) 
                → Spine Γ (L1 ++ L2) L+ U
spine-↑∧⁺ {L1 = []} () pf S InA InB id⁻
spine-↑∧⁺ {L1 = []} {[]} {[]} () pf S InA InB (↑L-cons pf₁ N₁)
spine-↑∧⁺ {L1 = []} {[]} {x ∷ L+} Len pf S InA InB (↑L-cons pf₁ N₁) = {!!}
spine-↑∧⁺ {L1 = []} {x ∷ L2} {L+} Len pf S InA InB (↑L-cons pf₁ N₁)
  with spine-↑∧⁺-+ {L1 = L+} {L2 = []} {N = {!!}} {!!} pf S InA InB N₁
... | Z rewrite concat-nil L+ = Z

-- Stupid pattern match for Agda
spine-↑∧⁺ {L1 = ._ ∷ []} {L+ = L+} {N = N} Len pf S InA InB (↑L-cons {x = x} pf₁ N₁) 
   with length-append-suc {L = L+} {X = x}
... | N' , Eq rewrite Eq =  ↑L-cons pf₁ (spine-↑∧⁺  {L1 = []} {N = {!!}} {!!} pf S InA InB N₁)
spine-↑∧⁺ {L1 = ._ ∷ []} Len pf S InA InB (⊃L {A₁} {B₁} V Sp) = ⊃L V (spine-↑∧⁺ {L1 = B₁ ∷ []} refl pf S InA InB Sp) 
spine-↑∧⁺ {L1 = ._ ∷ []} Len pf S InA InB (∧⁻L₁ {A₁} {B₁} Sp) = ∧⁻L₁ (spine-↑∧⁺ {L1 = A₁ ∷ []}  refl pf S InA InB Sp ) 
spine-↑∧⁺ {L1 = ._ ∷ []} Len pf S InA InB (∧⁻L₂ {A₁} {B₁} Sp) = ∧⁻L₂ (spine-↑∧⁺ {L1 = B₁ ∷ []}  refl pf S InA InB Sp)
spine-↑∧⁺ {L1 = ._ ∷ x₁ ∷ L1} Len pf S InA InB (↑L-cons pf₁ N₁) = 
  ↑L-cons pf₁ (spine-↑∧⁺  {L1 = x₁ ∷ L1} refl pf S InA InB N₁) 
spine-↑∧⁺ {L1 = ._ ∷ x₁ ∷ L1} Len pf S InA InB (⊃L {A₁} {B₁} V Sp) = 
  ⊃L V (spine-↑∧⁺ {L1 = B₁ ∷ x₁ ∷ L1} refl pf S InA InB Sp)
spine-↑∧⁺ {L1 = ._ ∷ x₁ ∷ L1} Len pf S InA InB (∧⁻L₁ {A₁} {B₁} Sp) = 
   ∧⁻L₁ (spine-↑∧⁺ {L1 = A₁ ∷ x₁ ∷ L1} refl pf S InA InB Sp)
spine-↑∧⁺ {L1 = ._ ∷ x₁ ∷ L1} Len pf S InA InB (∧⁻L₂ {A₁} {B₁} Sp) = 
  ∧⁻L₂ (spine-↑∧⁺ {L1 = B₁ ∷ x₁ ∷ L1} refl pf S InA InB Sp)



-- It is possible to remove a loaded shifted positive conjunction if its
-- two (shifted) components are already in the context
focL-↑∧⁺-step : ∀{Γ A B L1 L2 U}  
                (pf : stable U) 
                (S : suspnormal U)
                (InA : Pers (↑ A) ∈ Γ) 
                (InB : Pers (↑ B) ∈ Γ) 
                (Sp : Spine-l Γ (L1 ++ ↑ (A ∧⁺ B) ∷ L2) U) 
                → Spine-l Γ (L1 ++ L2) U
focL-↑∧⁺-step {L1 = L1} pf S InA InB (focL-step {A₁} pf₁ In Sp) = 
  focL-step pf₁ In (focL-↑∧⁺-step {L1 = A₁ ∷ L1} pf₁ S InA InB Sp)
focL-↑∧⁺-step {L1 = []} {[]} pf () InA InB (focL-end pf₁ id⁻)
focL-↑∧⁺-step {L1 = []} {[]} 
  pf 
  S 
  InA 
  InB 
  (focL-end pf₁ (↑L-cons pf₂ (↑L-nil pf₃ (∧⁺L N)))) 
    = focL-step pf₃ InB
      (focL-step pf₃ InA
       (focL-end pf₃ (↑L-cons pf₃ (↑L-cons pf₃ (↑L-nil pf₃ N))))) 
focL-↑∧⁺-step {L1 = []} {x ∷ L2} pf S InA InB (focL-end pf₁ N) = focL-end pf₁ (spine-↑∧⁺ {L1 = []}  {L2 = x ∷ L2} refl pf₁ S InA InB N) 
focL-↑∧⁺-step {L1 = x ∷ L1} pf S InA InB (focL-end pf₁ N) = focL-end pf₁ (spine-↑∧⁺ {L1 = x ∷ L1} refl pf₁ S InA InB N) 





mutual
  value-∧⁺-context : ∀{Γ' Γ A B U} 
    → Value (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) U 
    → Value (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) U 
    
  term-∧⁺-context : ∀{Γ' Γ A B L U} 
    → suspnormal U 
    → Term  (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) L U 
    → Term (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) L U 

  spine-l-∧⁺-context : ∀{Γ' Γ L- A B U} 
      → suspnormal U --Used by focL-↑∧⁺-step 
      → Spine-l  (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) L- U 
      → Spine-l (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) L- U 
  
  spine-∧⁺-context : ∀{Γ' Γ L- L+ A B U} 
      → suspnormal U
      → Spine  (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) L- L+ U 
      → Spine (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) L- L+ U 
  
  
  spine-∧⁺-context S id⁻ = id⁻
  spine-∧⁺-context {Γ'} S (↑L-cons pf N) = ↑L-cons pf (spine-∧⁺-context {Γ'} S N)
  spine-∧⁺-context {Γ'} S (↑L-nil pf N) = ↑L-nil pf (term-∧⁺-context {Γ'} S N)
  spine-∧⁺-context {Γ'} S (⊃L V Sp) = ⊃L (value-∧⁺-context {Γ'} V) (spine-∧⁺-context {Γ'} S Sp) 
  spine-∧⁺-context {Γ'} S (∧⁻L₁ Sp) = ∧⁻L₁ (spine-∧⁺-context {Γ'} S Sp)
  spine-∧⁺-context {Γ'} S (∧⁻L₂ Sp) = ∧⁻L₂ (spine-∧⁺-context {Γ'} S Sp) 
  
  spine-l-∧⁺-context {Γ'} S (focL-step pf In Sp) with fromctx Γ' In 
  -- * Pers (↑ (A ∧⁺ B)) was loaded 
  spine-l-∧⁺-context {Γ'} {Γ} {L- } {A = A} {B = B} S (focL-step pf In Sp) | inj₁ refl = 
    focL-↑∧⁺-step 
      {Γ = Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ} 
      {L1 = []}
      {L2 = L- }
      pf 
      S
      (in-append-right {L1 = Γ'} (here refl)) 
      (in-append-right {L1 = Γ'} (there (here refl)) ) 
      (spine-l-∧⁺-context {Γ'} S Sp) 
  -- * Something in Γ Γ' was loaded
  spine-l-∧⁺-context {Γ'} S (focL-step pf In Sp) | inj₂ y = focL-step pf (in-append-double-weak {L1 = Γ'} y) (spine-l-∧⁺-context {Γ'} S Sp)
  spine-l-∧⁺-context {Γ'} S (focL-end pf Sp) = focL-end pf (spine-∧⁺-context {Γ'} S Sp)


  value-∧⁺-context {Γ'} (id⁺ v) with fromctx Γ' v 
  value-∧⁺-context (id⁺ v) | inj₁ ()
  value-∧⁺-context {Γ'} (id⁺ v) | inj₂ y = id⁺ (in-append-double-weak {L1 = Γ'} y) 
  value-∧⁺-context {Γ'} (↓R N) = ↓R (term-∧⁺-context {Γ'} tt N)
  value-∧⁺-context {Γ'} (∨R₁ V) = ∨R₁ (value-∧⁺-context {Γ'} V)
  value-∧⁺-context {Γ'} (∨R₂ V) = ∨R₂ (value-∧⁺-context {Γ'}  V)
  value-∧⁺-context ⊤⁺R = ⊤⁺R
  value-∧⁺-context {Γ'} (∧⁺R V₁ V₂) = ∧⁺R (value-∧⁺-context {Γ'}  V₁) (value-∧⁺-context {Γ'}  V₂) 

  term-∧⁺-context {Γ'} S (focR V) = focR (value-∧⁺-context {Γ'} V)
  term-∧⁺-context {Γ'} S (focL-init pf Sp) = focL-init pf (spine-l-∧⁺-context {Γ'} S Sp)
  term-∧⁺-context {Γ'} S (η⁺ {Q} N) = η⁺ (term-∧⁺-context {HSusp (a Q ⁺) ∷ Γ'} S N)
  term-∧⁺-context {Γ'} S (↓L {A₁} N) = ↓L (term-∧⁺-context {Pers A₁ ∷ Γ'} S N)
  term-∧⁺-context {Γ'} S ⊥L = ⊥L
  term-∧⁺-context {Γ'} S (∨L N₁ N₂) = ∨L (term-∧⁺-context {Γ'} S N₁) (term-∧⁺-context {Γ'} S N₂)
  term-∧⁺-context {Γ'} S (⊤⁺L N) = ⊤⁺L (term-∧⁺-context {Γ'} S N)
  term-∧⁺-context {Γ'} S (∧⁺L N) = ∧⁺L (term-∧⁺-context {Γ'} S N)
  term-∧⁺-context {Γ'} S (η⁻ N) = η⁻ (term-∧⁺-context {Γ'} tt N)
  term-∧⁺-context {Γ'} S (↑R N) = ↑R (term-∧⁺-context {Γ'} tt N)
  term-∧⁺-context {Γ'} S (⊃R N) = ⊃R (term-∧⁺-context {Γ'} tt N)
  term-∧⁺-context {Γ'} S ⊤⁻R = ⊤⁻R
  term-∧⁺-context {Γ'} S (∧⁻R N₁ N₂) = ∧⁻R (term-∧⁺-context {Γ'} tt N₁) (term-∧⁺-context {Γ'} tt N₂) 







postulate
  spinel-↑pers : ∀{Γ1 Γ2 A B U} 
    → Spine-l (Γ1 ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ2) [] U
    → Spine-l (Γ1 ++ Pers (↑ (A ∧⁺ B)) ∷ Γ2) [] U
{-
spinel-↑pers {Γ1} (focL-step pf In Sp) with fromctx Γ1  In
spinel-↑pers (focL-step pf In Sp) | inj₁ refl = {!!}
spinel-↑pers (focL-step {Y} pf In Sp) | inj₂ y = {!!} 
spinel-↑pers (focL-end pf ()) 

value-↑pers : ∀{A B Γ1 Γ2 U} 
  → Value (Γ1 ++ Pers (↑ A)  ∷ Pers  (↑ B) ∷ Γ2) U 
  → Value (Γ1 ++ Pers (↑ (A  ∧⁺ B)) ∷ Γ2) U
value-↑pers V = {!!} 
-}





postulate
  term-↑pers : ∀{A B Γ1 Γ2 L U} 
    → Term (Γ1 ++ Pers (↑ A)  ∷ Pers  (↑ B) ∷ Γ2) L U 
    → Term (Γ1 ++ Pers (↑ (A  ∧⁺ B)) ∷ Γ2) L U
{-
term-↑pers {Γ1 = Γ1} {L = []} (focR V) = focR (value-↑pers {Γ1 = Γ1} V)
term-↑pers {Γ1 = Γ1} {L = []} (focL-init pf Sp) = focL-init pf (spinel-↑pers {Γ1} Sp)
term-↑pers {L = []} (η⁻ N) = {!!}
term-↑pers {L = []} (↑R N) = {!!}
term-↑pers {L = []} (⊃R N) = {!!}
term-↑pers {L = []} ⊤⁻R = {!!}
term-↑pers {Γ1 = Γ1} {L = []} (∧⁻R N₁ N₂) = ∧⁻R (term-↑pers {Γ1 = Γ1} N₁) (term-↑pers {Γ1 = Γ1} N₂) 
term-↑pers {L = x ∷ L} T = {!!} 
-}