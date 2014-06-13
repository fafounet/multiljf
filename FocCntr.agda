open import Data.List
open import Data.List.Any
open import Data.Product
open Membership-≡
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])

open import ListExtra

open import Foc
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
cntr-pers-gen-term {L1 = []} pf S ⊥L In = {!f!}
cntr-pers-gen-term {L1 = []} pf S (∨L N₁ N₂) In = {!!}
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