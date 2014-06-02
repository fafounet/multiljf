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
open import Identity

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

-- Cf FocAdmissible
--cntr-pers-term-bis : ∀{Γ A L+ U} → Term (Pers A ∷ Γ) (↓ A ∷ L+) U → Term Γ (↓ A ∷ L+) U
--cntr-pers-term-bis {Γ} {A} (↓L N) =  ↓L (cntr (Pers A ∷ Γ) (here refl) N)  




cntr-+-[]-spine : ∀{Γ Y L+ U}
  → stable U 
  → (X : Type ⁺) 
  → Spine Γ [] ((Y ∷ L+) ++ [ X ]) U 
  → Pers (↑ X) ∈ Γ
  → Spine Γ [] (Y ∷ L+) U

cntr-+-[]-spine pf X (↑L-nil pf₁ N) In = ↑L-nil pf₁ (cntr-pers-term pf₁ N In)



cntr-+-spine : ∀{Γ X L- L+ U} → Spine Γ L- ( X ∷ X ∷ L+) U → Spine Γ L- (X ∷ L+) U
cntr-+-spine (↑L-cons pf N) = ↑L-cons pf (cntr-+-spine N)
cntr-+-spine (↑L-nil pf N) = {!!}
cntr-+-spine (⊃L V Sp) = ⊃L V (cntr-+-spine Sp)
cntr-+-spine (∧⁻L₁ Sp) = ∧⁻L₁ (cntr-+-spine Sp)
cntr-+-spine (∧⁻L₂ Sp) = ∧⁻L₂ (cntr-+-spine Sp) 


cntr-⁻-spine : ∀{Γ X L- L+ U} → Spine Γ (X ∷ X ∷ L-) L+ U → Spine Γ (X ∷ L-) L+ U
cntr-⁻-spine {X = ↑ x} {L+ = []} (↑L-cons pf (↑L-cons pf₁ N)) = {!!}
cntr-⁻-spine {X = ↑ X} {L+ = x ∷ L+} (↑L-cons pf N) = {!!}
cntr-⁻-spine (⊃L V Sp) = {!!}
cntr-⁻-spine (∧⁻L₁ Sp) = {!!}
cntr-⁻-spine (∧⁻L₂ Sp) = {!!} 

-- The following is not true:
-- cntr-hsusp-term : ∀{Γ X L+ U} → Term Γ (X ∷ L+) U → HSusp X ∈ Γ → Term Γ L+ U
-- due to the following:
cntr-term-absurd : ∀{Q} → Term [ HSusp (⊥⁺) ]  [ ⊥⁺ ]  (Susp (a Q ⁻)) → Term [ HSusp (⊥⁺) ]  []  (Susp (a Q ⁻)) → ⊥
cntr-term-absurd ⊥L (focL-init pf (focL-step pf₁ (here ()) Sp))
cntr-term-absurd ⊥L (focL-init pf (focL-step pf₁ (there ()) Sp))
cntr-term-absurd ⊥L (focL-init pf (focL-end pf₁ ()))


cntr-term-hsusp : ∀{Γ X L+ U} → Term (HSusp X ∷ Γ) L+ U → X ∈ L+ → Term Γ L+ U
cntr-term-hsusp T In = {!expand⁺ T!} 
{-cntr-term-hsusp (focR V) ()
cntr-term-hsusp (focL-init pf Sp) ()
cntr-term-hsusp (η⁺ N) (here refl) = {!cntr-term-hsusp (cntr ? ? N) ?!}
cntr-term-hsusp (η⁺ N) (there In) = {!!}
cntr-term-hsusp (↓L N) In = {!!}
cntr-term-hsusp ⊥L In = ⊥L
cntr-term-hsusp (∨L N₁ N₂) In = {!!}
cntr-term-hsusp (⊤⁺L N) In = {!!}
cntr-term-hsusp (∧⁺L N) (here refl) = {!!}
cntr-term-hsusp (∧⁺L N) (there In) = ∧⁺L (cntr-term-hsusp N (there (there In)) )
cntr-term-hsusp (η⁻ N) In = η⁻ (cntr-term-hsusp N In)
cntr-term-hsusp (↑R N) In = ↑R (cntr-term-hsusp N In)
cntr-term-hsusp (⊃R N) In = ⊃R (cntr-term-hsusp N (there In))
cntr-term-hsusp ⊤⁻R In = ⊤⁻R
cntr-term-hsusp (∧⁻R N₁ N₂) In = ∧⁻R (cntr-term-hsusp N₁ In) (cntr-term-hsusp N₂ In) -}


hmm : ∀{Q} → Term [ HSusp (a Q ⁺) ] [ a Q ⁺ ] (True ( a Q ⁺))
hmm = λ {Q} → η⁺ (focR (id⁺ (here refl))) 

hmm2 : ∀{Q} → Term [] [ a Q ⁺ ] (True ( a Q ⁺))
hmm2 = λ {Q} → η⁺ (focR (id⁺ (here refl))) 