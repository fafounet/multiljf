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


module FocUpDisj where


value-∨-context : ∀{Γ' Γ A B U} 
  → Value  (Γ' ++ Pers (↑ (A ∨ B)) ∷ Γ) U 
  → Value (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) U 

term-∨-context : ∀{Γ' Γ A B L U} 
  → suspnormal U 
  → Term  (Γ' ++ Pers (↑ (A ∨ B)) ∷ Γ) L U 
  → Term (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) L U 

spinel-∨-context : ∀{Γ' Γ A B L U} 
  → suspnormal U 
  → Spine-l (Γ' ++ Pers (↑ (A ∨ B)) ∷ Γ) L U 
  → Spine-l (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) L U 

spine-∨-context : ∀{Γ' Γ A B L- L+ U} 
  → suspnormal U 
  → Spine (Γ' ++ Pers (↑ (A ∨ B)) ∷ Γ) L- L+  U 
  → Spine (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) L- L+ U 



value-∨-context {Γ'}  (id⁺ v) with fromctx Γ' v 
value-∨-context (id⁺ v) | inj₁ ()
value-∨-context {Γ'} {A = A} (id⁺ v) | inj₂ y = id⁺ (in-append-double-weak {Y = Pers (↑ A)} {L1 = Γ'}  y) 
value-∨-context {Γ'} (↓R N) = ↓R (term-∨-context {Γ' = Γ'} tt N)
value-∨-context {Γ'} (∨R₁ V) = ∨R₁ (value-∨-context {Γ'} V)
value-∨-context {Γ'} (∨R₂ V) = ∨R₂ (value-∨-context {Γ'} V)
value-∨-context ⊤⁺R = ⊤⁺R
value-∨-context {Γ'} (∧⁺R V₁ V₂) = ∧⁺R (value-∨-context {Γ'} V₁) (value-∨-context {Γ'} V₂) 



term-∨-context {Γ'}  pf (focR V) = focR (value-∨-context {Γ'}  V) 
term-∨-context {Γ'}  pf (focL-init pf₁ Sp) = focL-init pf₁ (spinel-∨-context {Γ'} pf Sp)
term-∨-context {Γ'}  pf (η⁺ {Q} N) = η⁺ (term-∨-context {HSusp (a Q ⁺) ∷ Γ'}  pf N)
term-∨-context {Γ'}  pf (↓L {A₁} N) = ↓L (term-∨-context {Pers A₁ ∷ Γ'}  pf N)
term-∨-context {Γ'}  pf ⊥L = ⊥L
term-∨-context {Γ'}  pf (∨L N₁ N₂) = ∨L (term-∨-context {Γ'}  pf N₁) (term-∨-context {Γ'}  pf N₂)
term-∨-context {Γ'}  pf (⊤⁺L N) = ⊤⁺L (term-∨-context {Γ'}  pf N)
term-∨-context {Γ'}  pf (∧⁺L N) = ∧⁺L (term-∨-context {Γ'}  pf N)
term-∨-context {Γ'}  pf (η⁻ N) = η⁻ (term-∨-context {Γ'}  tt N)
term-∨-context {Γ'}  pf (↑R N) = ↑R (term-∨-context {Γ'}  tt N)
term-∨-context {Γ'}  pf (⊃R N) = ⊃R (term-∨-context {Γ'}  tt N)
term-∨-context {Γ'}  pf ⊤⁻R = ⊤⁻R
term-∨-context {Γ'}  pf (∧⁻R N₁ N₂) = ∧⁻R (term-∨-context {Γ'}  tt N₁) (term-∨-context {Γ'}  tt N₂)

spinel-∨-context {Γ'} S (focL-step pf In Sp) with fromctx Γ' In
spinel-∨-context S (focL-step pf In Sp) | inj₁ refl = {!!}
spinel-∨-context {Γ'} {A = A} S (focL-step pf In Sp) | inj₂ y = focL-step pf (in-append-double-weak {Y = Pers (↑ A)} {L1 = Γ'} y) (spinel-∨-context {Γ'} S Sp)  
spinel-∨-context {Γ'} S (focL-end pf Sp) = focL-end pf (spine-∨-context {Γ'} S Sp)

spine-∨-context S id⁻ = id⁻
spine-∨-context {Γ'} S (↑L-cons pf N) = ↑L-cons pf (spine-∨-context {Γ'} S N)
spine-∨-context {Γ'} S (↑L-nil pf N) = ↑L-nil pf {!!}
spine-∨-context {Γ'} S (⊃L V Sp) = ⊃L (value-∨-context {Γ'} V) (spine-∨-context {Γ'}  S Sp) 
spine-∨-context {Γ'} S (∧⁻L₁ Sp) = ∧⁻L₁ (spine-∨-context {Γ'} S Sp)
spine-∨-context {Γ'} S (∧⁻L₂ Sp) = ∧⁻L₂ (spine-∨-context {Γ'} S Sp) 