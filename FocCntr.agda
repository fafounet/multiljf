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
open import FocAdmissible

open import NatExtra
open import ListExtra

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


cntr-pers-term-bis : ∀{Γ A L+ U} → Term (Pers A ∷ Γ) (↓ A ∷ L+) U → Term Γ (↓ A ∷ L+) U
cntr-pers-term-bis {Γ} {A} (↓L N) =  ↓L (cntr (Pers A ∷ Γ) (here refl) N)

cntr-pers-term-bis-gen : ∀{Γ Γ' A L+ U} → Term (Γ' ++ Pers A ∷ Γ) L+ U → ↓ A ∈ L+ → Term (Γ' ++ Γ) L+ U
cntr-pers-term-bis-gen {Γ' = Γ'} (↓L N) (here refl) = ↓L (cntr-there Γ' N)   
cntr-pers-term-bis-gen {Γ' = Γ'} (η⁺ {Q} N) (there In) = 
  η⁺ (cntr-pers-term-bis-gen {Γ' = HSusp (a Q ⁺) ∷ Γ'} N In)
cntr-pers-term-bis-gen {Γ' = Γ'} (↓L {A₁} N) (there In) = 
  ↓L (cntr-pers-term-bis-gen {Γ' = Pers A₁ ∷ Γ'} N In)
cntr-pers-term-bis-gen ⊥L (there In) = ⊥L
cntr-pers-term-bis-gen {Γ' = Γ'} (∨L N₁ N₂) (there In) = 
  ∨L (cntr-pers-term-bis-gen {Γ' = Γ'} N₁ (there In) ) (cntr-pers-term-bis-gen {Γ' = Γ'} N₂ (there In)) 
cntr-pers-term-bis-gen {Γ' = Γ'} (⊤⁺L N) (there In) = ⊤⁺L (cntr-pers-term-bis-gen {Γ' = Γ'} N In)
cntr-pers-term-bis-gen {Γ' = Γ'} (∧⁺L N) (there In) = ∧⁺L (cntr-pers-term-bis-gen {Γ' = Γ'} N (there (there In))) 







-- cntr-term-hsusp : ∀{Γ X L+ U} → Term (HSusp X ∷ Γ) L+ U → X ∈ L+ → Term Γ L+ U
{-
Could to be true ...
hmm : ∀{Q R } → Term [ HSusp (a Q ⁺ ∧⁺  a R ⁺) ] [ a Q ⁺ ∧⁺  a R ⁺ ] (True ( a Q ⁺ ∧⁺  a R ⁺))
hmm = λ {Q} {R} → ∧⁺L (η⁺ (η⁺ (focR (id⁺ (there (there (here refl))))))) 

hmm2 : ∀{Q R } → Term [] [ a Q ⁺ ∧⁺  a R ⁺ ] (True ( a Q ⁺ ∧⁺  a R ⁺))
hmm2 = λ {Q} {R} →
           ∧⁺L
           (η⁺ (η⁺ (focR (∧⁺R (id⁺ (there (here refl))) (id⁺ (here refl)))))) 
-}

cntr-term-hsusp-lit : ∀{Γ1 Γ2 Q L+ U} → Term (Γ1 ++ HSusp (a Q ⁺) ∷ Γ2) L+ U → (a Q ⁺) ∈ L+ → Term (Γ1 ++ Γ2) L+ U
cntr-term-hsusp-lit (focR V) ()
cntr-term-hsusp-lit (focL-init pf Sp) ()
cntr-term-hsusp-lit {Γ1} (η⁺ {Q} N) (here refl) = η⁺ (cntr-there Γ1 N)
cntr-term-hsusp-lit {Γ1} (η⁺ {Q₁} N) (there In) = η⁺ (cntr-term-hsusp-lit {Γ1 = HSusp (a Q₁ ⁺) ∷ Γ1} N In)
cntr-term-hsusp-lit (↓L N) (here ())
cntr-term-hsusp-lit {Γ1} (↓L {A} N) (there In) =  ↓L (cntr-term-hsusp-lit {Γ1 = Pers A ∷ Γ1} N In)
cntr-term-hsusp-lit ⊥L In = ⊥L
cntr-term-hsusp-lit (∨L N₁ N₂) (here ())
cntr-term-hsusp-lit {Γ1} (∨L N₁ N₂) (there In) = 
  ∨L (cntr-term-hsusp-lit {Γ1} N₁ (there In)) (cntr-term-hsusp-lit {Γ1}  N₂ (there In) ) 
cntr-term-hsusp-lit (⊤⁺L N) (here ())
cntr-term-hsusp-lit {Γ1}  (⊤⁺L N) (there In) = ⊤⁺L (cntr-term-hsusp-lit {Γ1}  N In)
cntr-term-hsusp-lit (∧⁺L N) (here ())
cntr-term-hsusp-lit {Γ1}  (∧⁺L N) (there In) = ∧⁺L (cntr-term-hsusp-lit {Γ1}  N (there (there In))) 
cntr-term-hsusp-lit {Γ1}  (η⁻ N) In = η⁻ (cntr-term-hsusp-lit {Γ1}  N In)
cntr-term-hsusp-lit {Γ1}  (↑R N) In = ↑R (cntr-term-hsusp-lit {Γ1}  N In)
cntr-term-hsusp-lit {Γ1}  (⊃R N) In = ⊃R (cntr-term-hsusp-lit {Γ1}  N (there In))
cntr-term-hsusp-lit ⊤⁻R In = ⊤⁻R
cntr-term-hsusp-lit {Γ1}  (∧⁻R N₁ N₂) In = ∧⁻R (cntr-term-hsusp-lit {Γ1}  N₁ In) (cntr-term-hsusp-lit {Γ1}  N₂ In) 



cntr-+-term-gen : ∀{Γ X L+ U N } → Term Γ (X ∷ L+) U → X ∈ L+ → size-list-formulas (X ∷ L+) ≡ N → Term Γ L+ U
cntr-+-term-gen-helper : ∀{Γ X L+ U N } → Term Γ (X ∷ L+) U → X ∈ L+ → N >′ size-list-formulas (X ∷ L+)  → Term Γ L+ U
--
cntr-+-term-gen-helper T In (>′-refl m≡n) = cntr-+-term-gen T In refl 
cntr-+-term-gen-helper T In (>′-step Ineq) = cntr-+-term-gen-helper T In Ineq 
--
cntr-+-term-gen (η⁺ N) In S =  cntr-term-hsusp-lit {Γ1 = []} N In  
cntr-+-term-gen {L+ = []} (↓L N) () _
cntr-+-term-gen {L+ = ._ ∷ L+} (↓L N) (here refl) S = cntr-pers-term-bis N
cntr-+-term-gen {L+ = x ∷ L+} (↓L N) (there In) S = cntr-pers-term-bis-gen {Γ' = []} N (there In) 
cntr-+-term-gen ⊥L In S = term-⊥-adm In 
cntr-+-term-gen (∨L {A} {B} N₁ N₂) In S with in-split In
... | L1 , L2 , Eq rewrite Eq with term-∨L-inv {L1 = A ∷ L1} N₁ | term-∨L-inv {L1 = B ∷ L1} N₂
... | T1 , T2 | T'1 , T'2 = 
  term-∨L-adm {L1 = L1} 
    (cntr-+-term-gen-helper T1 (in-append-cons {L1 = L1}) (size-list-helper1 {A = A} {L1 = L1}  S)) 
    (cntr-+-term-gen-helper T'2 (in-append-cons {L1 = L1}) (size-list-helper2 {A = A} {L1 = L1} S)) 
cntr-+-term-gen (⊤⁺L N) In S = N
cntr-+-term-gen (∧⁺L {A = A} {B = B} N) In S with in-split In
... | L1 , L2 , Eq rewrite Eq = 
  term-∧⁺-adm {L1 = L1}
  (cntr-+-term-gen-helper 
    (cntr-+-term-gen-helper
        (term-∧⁺-inv {L1 = A ∷ B ∷ L1} N) 
        (there (in-append-right {L1 = L1} (here refl) ) ) 
        (size-list-helper3 {A = A} {B = B} {L1 = L1} S))
    (in-append-right {L1 = L1} (there (here refl))) 
    (size-list-helper4 {A = A} {L1 = L1}  S))

cntr-+-term : ∀{Γ X L+ U} →  Term Γ (X ∷ X ∷ L+) U → Term Γ (X ∷ L+) U 
cntr-+-term T = cntr-+-term-gen T (here refl) refl  


cntr-+-[]-spine : ∀{Γ Y L+ U}
  → stable U 
  → (X : Type ⁺) 
  → Spine Γ [] ((Y ∷ L+) ++ [ X ]) U 
  → Pers (↑ X) ∈ Γ
  → Spine Γ [] (Y ∷ L+) U
cntr-+-[]-spine pf X (↑L-nil pf₁ N) In = ↑L-nil pf₁ (cntr-pers-term pf₁ N In)


cntr-+-spine-gen : ∀{Γ X L- L+ U} → Spine Γ L- (X ∷ L+) U → X ∈ L+ → Spine Γ L- L+ U
cntr-+-spine-gen (↑L-cons pf N) In = ↑L-cons pf (cntr-+-spine-gen N (in-append-left In) ) 
cntr-+-spine-gen {L+ = []} (↑L-nil pf N) ()
cntr-+-spine-gen {L+ = x ∷ L+} (↑L-nil pf N) In = ↑L-nil pf (cntr-+-term-gen  N In refl ) 
cntr-+-spine-gen (⊃L V Sp) In = ⊃L V (cntr-+-spine-gen Sp In)
cntr-+-spine-gen (∧⁻L₁ Sp) In = ∧⁻L₁ (cntr-+-spine-gen Sp In)
cntr-+-spine-gen (∧⁻L₂ Sp) In = ∧⁻L₂ (cntr-+-spine-gen Sp In) 


cntr-+-spine : ∀{Γ X L- L+ U} → Spine Γ L- (X ∷ X ∷ L+) U → Spine Γ L- (X ∷ L+) U
cntr-+-spine Sp = cntr-+-spine-gen Sp (here refl) 


{- HARD! (if true ....)
  Requires generalized ⊃L inversion rule
  Need gsubst-gen ?

cntr-⁻-spine : ∀{Γ X L- L+ U} → Spine Γ (X ∷ X ∷ L-) L+ U → Spine Γ (X ∷ L-) L+ U
cntr-⁻-spine {X = ↑ x} {L+ = []} (↑L-cons pf (↑L-cons pf₁ N)) = ↑L-cons pf (cntr-+-spine N)
cntr-⁻-spine {X = ↑ X} {L+ = x ∷ L+} (↑L-cons pf N) = ↑L-cons pf {!!}
cntr-⁻-spine (⊃L V Sp) = {!!}
cntr-⁻-spine (∧⁻L₁ Sp) = {!!}
cntr-⁻-spine (∧⁻L₂ Sp) = {!!} 
-}


-- The following is not true:
-- cntr-hsusp-term : ∀{Γ X L+ U} → Term Γ (X ∷ L+) U → HSusp X ∈ Γ → Term Γ L+ U
-- due to the following:
cntr-term-absurd : ∀{Q} → Term [ HSusp (⊥⁺) ]  [ ⊥⁺ ]  (Susp (a Q ⁻)) → Term [ HSusp (⊥⁺) ]  []  (Susp (a Q ⁻)) → ⊥
cntr-term-absurd ⊥L (focL-init pf (focL-step pf₁ (here ()) Sp))
cntr-term-absurd ⊥L (focL-init pf (focL-step pf₁ (there ()) Sp))
cntr-term-absurd ⊥L (focL-init pf (focL-end pf₁ ()))

