open import Data.List
open import Data.List.Any
open import Data.Product
open Membership-≡
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])

open import ListExtra

open import Foc
open import FocSimpleProps
open import FocUpConj

module FocCntr where



cntr-pers-gen-term : ∀{Γ L1 L2 X U}
  → stable U 
  → suspnormal U
  → Term Γ (L1 ++ X ∷ L2) U 
  → Pers (↑ X) ∈ Γ 
  → Term Γ (L1 ++ L2) U

cntr-pers-gen-term {L1 = []} pf S (η⁺ N) In = {!!}
cntr-pers-gen-term {L1 = []} pf S (↓L N) In = {!!}
cntr-pers-gen-term {L1 = []} pf S ⊥L In = term-⊥-context-gen pf In
cntr-pers-gen-term {L1 = []} pf S (∨L N₁ N₂) In = {!∨L ? ? !}
cntr-pers-gen-term {L1 = []} pf S (⊤⁺L N) In = N
cntr-pers-gen-term {L1 = []} pf S (∧⁺L {A = A} {B = B} N) In with in-split In 
... | M1 , M2 , Eq rewrite Eq = 
  term-↑pers {A} {B} {M1} 
    (cntr-pers-gen-term 
        {L1 = []} 
        pf 
        S
        (cntr-pers-gen-term {L1 = []}  pf S (term-∧⁺-context {Γ' = M1} S N) (in-append-right {L1 = M1} (here refl))) 
        (in-append-right {L1 = M1} (there (here refl))))
  -- Requires term-∧⁺-context (thus suspnormal U as a condition)
--  cntr-pers-gen-term {L1 = {!!}} pf S (term-∧⁺-context {Γ' = {!M1!}} S N) {!!}
cntr-pers-gen-term {L1 = x ∷ L1} pf S T In = {!!} 


postulate 
  helper1 : ∀{a} {A : Set a} {Y : A} {L1 L2 X x} → Y ∷ (L1 ++ X ∷ L2) ++ [ x ] ≡ (Y ∷ L1) ++ X ∷ (L2 ++ [ x ])

postulate
  helper2 : ∀{a} {A : Set a} {Y : A} {L1 L2 x} → Y ∷ L1 ++ L2 ++ [ x ] ≡ (Y ∷ L1 ++ L2) ++ [ x ]

cntr-+-L-spine : ∀{Γ X L- Y L1 L2 U}
  → stable U 
  → suspnormal U
  → Spine Γ L- ((Y ∷ L1) ++ X ∷ L2) U 
  → Pers (↑ X) ∈ Γ
  → Spine Γ L- ((Y ∷ L1) ++ L2) U
-- Requires cntr-pers-gen-term and thus suspnormal U as a condition
cntr-+-L-spine {X = X} {Y = Y} {L1} {L2} pf S (↑L-cons {x} pf₁ N) In 
  rewrite helper1 {Y = Y} {L1} {L2} {X} {x} 
  with cntr-+-L-spine {L1 = L1} pf S N In
... | R1 rewrite helper2 {Y = Y} {L1} {L2} {x} = 
  ↑L-cons pf₁ R1 
cntr-+-L-spine {Y = Y} {L1} pf S (↑L-nil pf₁ N) In = ↑L-nil pf₁ (cntr-pers-gen-term {L1 = Y ∷ L1} pf S N In)
cntr-+-L-spine {L1 = L1} pf S (⊃L V Sp) In = ⊃L V (cntr-+-L-spine {L1 = L1} pf S Sp In)
cntr-+-L-spine {L1 = L1} pf S (∧⁻L₁ Sp) In = ∧⁻L₁ (cntr-+-L-spine {L1 = L1} pf S Sp In)
cntr-+-L-spine {L1 = L1} pf S (∧⁻L₂ Sp) In = ∧⁻L₂ (cntr-+-L-spine {L1 = L1} pf S Sp In) 
