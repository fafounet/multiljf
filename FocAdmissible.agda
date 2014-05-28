open import Data.List

module FocAdmissible where

open import Foc
open import FocProps

{- Is there a way to derive this for all rules???? -}
term-∧⁺-adm : ∀{Γ L2 A B U} → (L1 : List (Type ⁺)) → Term Γ (L1 ++ A ∷ B ∷ L2) U → Term Γ (L1 ++ A ∧⁺ B ∷ L2) U
term-∧⁺-adm [] T = ∧⁺L T
term-∧⁺-adm (._ ∷ xs) (η⁺ N) = η⁺ (term-∧⁺-adm xs N)
term-∧⁺-adm (._ ∷ xs) (↓L N) = ↓L (term-∧⁺-adm xs N)
term-∧⁺-adm (.⊥⁺ ∷ xs) ⊥L = ⊥L
term-∧⁺-adm (._ ∷ xs) (∨L {A₁} {B₁} N₁ N₂) = ∨L (term-∧⁺-adm (A₁ ∷ xs) N₁) (term-∧⁺-adm (B₁ ∷ xs) N₂)
term-∧⁺-adm (.⊤⁺ ∷ xs) (⊤⁺L N) = ⊤⁺L (term-∧⁺-adm xs N)
term-∧⁺-adm (._ ∷ xs) (∧⁺L {A = A₁} {B = B₁} N) = ∧⁺L (term-∧⁺-adm (A₁ ∷ B₁ ∷ xs) N)

postulate
  spine-∧⁺-adm : ∀{Γ L- L+ A B U} → Spine Γ L- (A ∷ B ∷ L+) U → Spine Γ L- (A ∧⁺ B ∷ L+) U


{-
 TODO: Prove/ HARD!! -}
spine-∨-adm : ∀{Γ L- L+ A B U} 
    → Spine Γ L- (A ∷ L+) U 
    → Spine Γ L- (B ∷ L+) U 
    → Spine Γ L- (A ∨ B ∷ L+) U


spine-∨-adm' : ∀{Γ L- L+ L'+ A B U} 
  → Spine Γ L- (A ∷ L+) U 
  → Spine Γ L- (B ∷ L'+) U 
  → Spine Γ L- (A ∨ B ∷ L+ ++ L'+) U

spine-∨-adm' (↑L-cons pf N) (↑L-cons pf₁ N₁) = ↑L-cons pf₁ (spine-∨-adm {!!} {!!}) --Weak spine + 
spine-∨-adm' (↑L-nil pf N) (↑L-nil pf₁ N₁) =  ↑L-nil pf₁ (∨L {!!} {!!} ) -- weak term +
spine-∨-adm' (⊃L V Sp) (⊃L V₁ Sp₁) =  ⊃L V (spine-∨-adm {!!} {!!} )  --Weak spine + 
spine-∨-adm' (∧⁻L₁ Sp) (∧⁻L₁ Sp₁) = ∧⁻L₁ (spine-∨-adm' Sp Sp₁ ) 
spine-∨-adm' (∧⁻L₁ Sp) (∧⁻L₂ Sp₁) with spine-possib-phases Sp
... | Z = {!!} 
spine-∨-adm' (∧⁻L₂ Sp) (∧⁻L₁ Sp₁) = {!!}
spine-∨-adm' (∧⁻L₂ Sp) (∧⁻L₂ Sp₁) = ∧⁻L₂ (spine-∨-adm' Sp Sp₁ ) 


spine-∨-adm {L- = []} (↑L-nil pf N) (↑L-nil pf₁ N₁) = ↑L-nil pf₁ (∨L N N₁)
spine-∨-adm {L- = a Q .⁻ ∷ L- } () Sp2
spine-∨-adm {L- = ↑ x ∷ L- } (↑L-cons pf N) (↑L-cons pf₁ N₁) = ↑L-cons pf₁ (spine-∨-adm N N₁)
spine-∨-adm {L- = A₁ ⊃ B₁ ∷ L- } (⊃L V Sp) (⊃L V₁ Sp₁) = ⊃L V (spine-∨-adm Sp Sp₁ ) 
spine-∨-adm {L- = ⊤⁻ ∷ L- } () Sp2
spine-∨-adm {L- = C ∧⁻ D ∷ L- } (∧⁻L₁ Sp) (∧⁻L₁ Sp₁) = ∧⁻L₁ (spine-∨-adm Sp Sp₁ )
spine-∨-adm {L- = C ∧⁻ D ∷ L- } (∧⁻L₁ Sp) (∧⁻L₂ Sp₁) = {!!}
spine-∨-adm {L- = C ∧⁻ D ∷ L- } (∧⁻L₂ Sp) (∧⁻L₁ Sp₁) = {!!}
spine-∨-adm {L- = C ∧⁻ D ∷ L- } (∧⁻L₂ Sp) (∧⁻L₂ Sp₁) = ∧⁻L₂ (spine-∨-adm Sp Sp₁ ) 




spine-∧⁻L₂-adm :  ∀{Γ L' L- L+ A B U}  → Spine Γ (L' ++ (B ∷ L-)) L+ U → Spine Γ (L' ++ (A ∧⁻ B) ∷ L-) L+ U
spine-∧⁻L₂-adm {L' = []} Sp = ∧⁻L₂ Sp
spine-∧⁻L₂-adm {L' = a Q .⁻ ∷ []} ()
spine-∧⁻L₂-adm {L' = a Q .⁻ ∷ x ∷ L'} ()
spine-∧⁻L₂-adm {L' = ↑ x ∷ []} (↑L-cons pf N) = ↑L-cons pf (∧⁻L₂ N)
spine-∧⁻L₂-adm {L' = ↑ x ∷ x₁ ∷ L'} (↑L-cons pf N) = ↑L-cons pf (spine-∧⁻L₂-adm {L' = x₁ ∷ L'} N) 
spine-∧⁻L₂-adm {L' = A₁ ⊃ B₁ ∷ []} (⊃L V Sp) = ⊃L V (spine-∧⁻L₂-adm {L' = B₁ ∷ []}  Sp)
spine-∧⁻L₂-adm {L' = A₁ ⊃ B₁ ∷ x₂ ∷ L'} (⊃L V Sp) = ⊃L V (spine-∧⁻L₂-adm {L' = B₁ ∷ x₂ ∷ L'} Sp)
spine-∧⁻L₂-adm {L' = ⊤⁻ ∷ []} ()
spine-∧⁻L₂-adm {L' = ⊤⁻ ∷ x ∷ L'} ()
spine-∧⁻L₂-adm {L' = A₁ ∧⁻ x₁ ∷ []} (∧⁻L₁ Sp) = ∧⁻L₁ (spine-∧⁻L₂-adm {L' = A₁ ∷ []} Sp)  
spine-∧⁻L₂-adm {L' = A₁ ∧⁻ x₁ ∷ []} (∧⁻L₂ Sp) = ∧⁻L₂ (spine-∧⁻L₂-adm {L' = x₁ ∷ []} Sp)
spine-∧⁻L₂-adm {L' = A₁ ∧⁻ x₁ ∷ x₂ ∷ L'} (∧⁻L₁ Sp) =  ∧⁻L₁ (spine-∧⁻L₂-adm {L' = A₁ ∷ x₂ ∷ L'} Sp)
spine-∧⁻L₂-adm {L' = A₁ ∧⁻ x₁ ∷ x₂ ∷ L'} (∧⁻L₂ Sp) = ∧⁻L₂ (spine-∧⁻L₂-adm {L' = x₁ ∷ x₂ ∷ L'} Sp)
  
postulate 
  spine-↑-adm : ∀{Γ L- L1 L2 A U} → Spine Γ L- ((L1 ++ [ A ]) ++ L2) U → Spine Γ (↑ A ∷ L-) (L1 ++ L2) U

-- The following is NOT admissible, if L- is an atom
-- spine-⊤⁺-adm :  ∀{Γ L- L+ U} → Spine Γ L- L+  U → Spine Γ L- (⊤⁺ ∷ L+) U