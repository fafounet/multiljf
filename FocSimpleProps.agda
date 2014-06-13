open import Data.List
open import Data.Empty
open import Data.Sum
open import Data.Unit
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open import Data.List.Any
open import Data.List.All
open import Data.Product
open Membership-≡

open import FocAdmissible
open import ListExtra
open import Foc


module FocSimpleProps where



term-⊥-context : ∀{Γ U} → stable U → Pers (↑ ⊥⁺) ∈ Γ  → Term Γ [] U
term-⊥-context pf (here refl) = 
  focL-init pf (focL-step pf (here refl) (focL-end pf (↑L-cons pf (↑L-nil pf ⊥L))) ) 
term-⊥-context pf (there In) = 
  focL-init pf (focL-step pf (there In) (focL-end pf (↑L-cons pf (↑L-nil pf ⊥L))))



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

------
------
  
--spine-∧-adm : ∀{Γ A B L1 L2 L+ U} → Spine Γ (L1 ++ (A ∧⁻ B) ∷ L2) L+ U → suspnormal U → Spine Γ (L1 ++ A ∷ B ∷ L2) L+ U


cntr-pers-gen-term : ∀{Γ L1 L2 X U}
  → stable U 
  → suspnormal U
  → Term Γ (L1 ++ X ∷ L2) U 
  → Pers (↑ X) ∈ Γ 
  → Term Γ (L1 ++ L2) U





spine-↑∧⁺-+ : ∀{Γ A B L L1 L2 U}  
                (pf : stable U) 
                (S : suspnormal U)
                (InA : Pers (↑ A) ∈ Γ) 
                (InB : Pers (↑ B) ∈ Γ) 
                (Sp : Spine Γ L (L1 ++ (A ∧⁺ B) ∷ L2)  U) 
                → Spine Γ L (L1 ++ L2) U
spine-↑∧⁺-+ {L = []} {[]} pf S InA InB (↑L-nil pf₁ (∧⁺L N)) = {!!}
spine-↑∧⁺-+ {L = []} {x ∷ L1} pf S InA InB Sp = {!!}
spine-↑∧⁺-+ {L = x ∷ L} pf S InA InB Sp = {!!}

spine-↑∧⁺ : ∀{Γ A B L1 L2 L+ U}  
                (pf : stable U) 
                (S : suspnormal U)
                (InA : Pers (↑ A) ∈ Γ) 
                (InB : Pers (↑ B) ∈ Γ) 
                (Sp : Spine Γ (L1 ++ ↑ (A ∧⁺ B) ∷ L2) L+ U) 
                → Spine Γ (L1 ++ L2) L+ U
spine-↑∧⁺ {L1 = []} pf () InA InB id⁻
spine-↑∧⁺ {L1 = []} pf S InA InB (↑L-cons pf₁ N) = {!!}
-- Stupid pattern match for Agda
spine-↑∧⁺ {L1 = ._ ∷ []} pf S InA InB (↑L-cons pf₁ N) = ↑L-cons pf₁ (spine-↑∧⁺ {L1 = []} pf S InA InB N) 
spine-↑∧⁺ {L1 = ._ ∷ []} pf S InA InB (⊃L {A₁} {B₁} V Sp) = ⊃L V (spine-↑∧⁺ {L1 = B₁ ∷ []} pf S InA InB Sp) 
spine-↑∧⁺ {L1 = ._ ∷ []} pf S InA InB (∧⁻L₁{A₁} {B₁} Sp) = ∧⁻L₁ (spine-↑∧⁺ {L1 = A₁ ∷ []} pf S InA InB Sp) 
spine-↑∧⁺ {L1 = ._ ∷ []} pf S InA InB (∧⁻L₂ {A₁} {B₁} Sp) = ∧⁻L₂ (spine-↑∧⁺ {L1 = B₁ ∷ []} pf S InA InB Sp) 
spine-↑∧⁺ {L1 = ._ ∷ x₁ ∷ L1} pf S InA InB (↑L-cons pf₁ N) = ↑L-cons pf₁ (spine-↑∧⁺ {L1 = x₁ ∷ L1} pf S InA InB N) 
spine-↑∧⁺ {L1 = ._ ∷ x₁ ∷ L1} pf S InA InB (⊃L {A₁} {B₁} V Sp) = ⊃L V (spine-↑∧⁺ {L1 = B₁ ∷ x₁ ∷ L1} pf S InA InB Sp) 
spine-↑∧⁺ {L1 = ._ ∷ x₁ ∷ L1} pf S InA InB (∧⁻L₁ {A₁} {B₁} Sp) =  ∧⁻L₁ (spine-↑∧⁺ {L1 = A₁ ∷ x₁ ∷ L1} pf S InA InB Sp) 
spine-↑∧⁺ {L1 = ._ ∷ x₁ ∷ L1} pf S InA InB (∧⁻L₂ {A₁} {B₁} Sp) = ∧⁻L₂ (spine-↑∧⁺ {L1 = B₁ ∷ x₁ ∷ L1} pf S InA InB Sp)  


focL-↑∧⁺-step : ∀{Γ A B L1 L2 U}  
                (pf : stable U) 
                (S : suspnormal U)
                (InA : Pers (↑ A) ∈ Γ) 
                (InB : Pers (↑ B) ∈ Γ) 
                (Sp : Spine-l Γ (L1 ++ ↑ (A ∧⁺ B) ∷ L2) U) 
                → Spine-l Γ (L1 ++ L2) U
focL-↑∧⁺-step {L1 = L1} pf S InA InB (focL-step {A₁} pf₁ In Sp) = 
  focL-step pf₁ In (focL-↑∧⁺-step {L1 = A₁ ∷ L1} pf₁ S InA InB Sp)
focL-↑∧⁺-step {L1 = L1} pf S InA InB (focL-end pf₁ Sp) = focL-end  pf₁ (spine-↑∧⁺ {L1 = L1} pf S InA InB Sp)




value-∧⁺-context : ∀{Γ' Γ A B U} 
  → Value (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) U 
  → Value (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) U 



spine-l-∧⁺-context : ∀{Γ' Γ L- A B U} 
  → suspnormal U --Used by focL-↑∧⁺-step 
  → Spine-l  (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) L- U 
  → Spine-l (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) L- U 
spine-l-∧⁺-context {Γ'} S (focL-step pf In Sp) with fromctx Γ' In 
spine-l-∧⁺-context {Γ'} {Γ} {A = A} {B = B} S (focL-step pf In Sp) | inj₁ refl = 
  focL-↑∧⁺-step 
    {Γ = Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ} 
    {L1 = []}
    pf 
    S
    (in-append-right {L1 = Γ'} (here refl)) 
    (in-append-right {L1 = Γ'} (there (here refl)) ) 
    (spine-l-∧⁺-context {Γ'} S Sp) 
spine-l-∧⁺-context S (focL-step pf In Sp) | inj₂ y = {!!}
spine-l-∧⁺-context S (focL-end pf Sp) = {!!}





term-∧⁺-context : ∀{Γ' Γ A B L U} 
  → suspnormal U 
  → Term  (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) L U 
  → Term (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) L U 

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





spinel-↑pers : ∀{Γ1 Γ2 A B U} 
  → Spine-l (Γ1 ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ2) [] U
  → Spine-l (Γ1 ++ Pers (↑ (A ∧⁺ B)) ∷ Γ2) [] U
spinel-↑pers {Γ1} (focL-step pf In Sp) with fromctx Γ1  In
spinel-↑pers (focL-step pf In Sp) | inj₁ refl = {!!}
spinel-↑pers (focL-step {Y} pf In Sp) | inj₂ y = {!!} 
spinel-↑pers (focL-end pf ()) 

value-↑pers : ∀{A B Γ1 Γ2 U} 
  → Value (Γ1 ++ Pers (↑ A)  ∷ Pers  (↑ B) ∷ Γ2) U 
  → Value (Γ1 ++ Pers (↑ (A  ∧⁺ B)) ∷ Γ2) U
value-↑pers V = {!!} 


term-↑pers : ∀{A B Γ1 Γ2 L U} 
  → Term (Γ1 ++ Pers (↑ A)  ∷ Pers  (↑ B) ∷ Γ2) L U 
  → Term (Γ1 ++ Pers (↑ (A  ∧⁺ B)) ∷ Γ2) L U
term-↑pers {Γ1 = Γ1} {L = []} (focR V) = focR (value-↑pers {Γ1 = Γ1} V)
term-↑pers {Γ1 = Γ1} {L = []} (focL-init pf Sp) = focL-init pf (spinel-↑pers {Γ1} Sp)
term-↑pers {L = []} (η⁻ N) = {!!}
term-↑pers {L = []} (↑R N) = {!!}
term-↑pers {L = []} (⊃R N) = {!!}
term-↑pers {L = []} ⊤⁻R = {!!}
term-↑pers {Γ1 = Γ1} {L = []} (∧⁻R N₁ N₂) = ∧⁻R (term-↑pers {Γ1 = Γ1} N₁) (term-↑pers {Γ1 = Γ1} N₂) 
term-↑pers {L = x ∷ L} T = {!!} 


cntr-pers-gen-term {L1 = []} pf S (η⁺ N) In = {!!}
cntr-pers-gen-term {L1 = []} pf S (↓L N) In = {!!}
cntr-pers-gen-term {L1 = []} pf S ⊥L In = {!!}
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




term-and-notand-absurd :  ∀{Γ Q L+ R}
  → Term Γ L+ (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺)))
  → All (λ x → x ≡ Pers (↑ (a Q ⁺)) ⊎ x ≡ Pers (↑ (a R ⁺)) ⊎  x ≡ HSusp (a Q ⁺)  ⊎  x ≡ HSusp (a R ⁺) ) Γ
  → All (λ x → x ≡ a Q ⁺ ⊎ x ≡ a R ⁺) L+
  → ⊥

spinel-and-notand-absurd : ∀{Γ Q L+ R}
 → Spine-l Γ L+ (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺))) 
 → All (λ x → x ≡ Pers (↑ (a Q ⁺)) ⊎ x ≡ Pers (↑ (a R ⁺))  ⊎  x ≡ HSusp (a Q ⁺)  ⊎  x ≡ HSusp (a R ⁺) ) Γ
 → All (\x → x ≡ (↑ (a Q ⁺)) ⊎ x ≡ (↑ (a R ⁺))) L+
 → ⊥ 

term-and-notand-absurd (η⁺ N) All1 (inj₁ refl ∷ All2) = term-and-notand-absurd N (inj₂ (inj₂ (inj₁ refl)) ∷ All1) All2
term-and-notand-absurd (η⁺ N) All1 (inj₂ refl ∷ All2) = term-and-notand-absurd N (inj₂ (inj₂ (inj₂ refl)) ∷ All1) All2 
term-and-notand-absurd (↓L N) All1 (inj₁ () ∷ All2)
term-and-notand-absurd (↓L N) All1 (inj₂ () ∷ All2)
term-and-notand-absurd ⊥L All1 (inj₁ () ∷ All2)
term-and-notand-absurd ⊥L All1 (inj₂ () ∷ All2)
term-and-notand-absurd (∨L N₁ N₂) All1 (inj₁ () ∷ All2)
term-and-notand-absurd (∨L N₁ N₂) All1 (inj₂ () ∷ All2)
term-and-notand-absurd (⊤⁺L N) All1 (inj₁ () ∷ All2)
term-and-notand-absurd (⊤⁺L N) All1 (inj₂ () ∷ All2)
term-and-notand-absurd (∧⁺L N) All1 (inj₁ () ∷ All2)
term-and-notand-absurd (∧⁺L N) All1 (inj₂ () ∷ All2) 
term-and-notand-absurd (focL-init pf Sp) All1 [] = spinel-and-notand-absurd Sp All1 [] 

spine-and-notand-absurd : ∀{Γ Q L+ L- R}
  → All (λ x → x ≡ Pers (↑ (a Q ⁺)) ⊎ x ≡ Pers (↑ (a R ⁺)) ⊎  x ≡ HSusp (a Q ⁺)  ⊎  x ≡ HSusp (a R ⁺)   ) Γ
  → Spine Γ L+ L- (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺))) 
  → All (\x → x ≡ (↑ (a Q ⁺)) ⊎ x ≡ (↑ (a R ⁺))) L+
  → All (\x → x ≡ a Q ⁺ ⊎ x ≡ a R ⁺) L-
  → ⊥ 
spine-and-notand-absurd All id⁻ (inj₁ () ∷ In1) In2
spine-and-notand-absurd All id⁻ (inj₂ () ∷ In1) In2 
spine-and-notand-absurd All (↑L-cons pf N) (inj₁ refl ∷ In1) In2 = 
  spine-and-notand-absurd All N In1 (all-append (inj₁ refl) In2 )  
spine-and-notand-absurd All (↑L-cons pf N) (inj₂ refl ∷ In1) In2 = 
  spine-and-notand-absurd All N In1 (all-append (inj₂ refl) In2) 
spine-and-notand-absurd {Γ} {Q = Q} {R = R} All (↑L-nil pf N) In1 In2 = 
  term-and-notand-absurd N 
    All
    In2
spine-and-notand-absurd All (⊃L V Sp) (inj₁ () ∷ In1) In2
spine-and-notand-absurd All (⊃L V Sp) (inj₂ () ∷ In1) In2
spine-and-notand-absurd All (∧⁻L₁ Sp) (inj₁ () ∷ In1) In2
spine-and-notand-absurd All (∧⁻L₁ Sp) (inj₂ () ∷ In1) In2
spine-and-notand-absurd All (∧⁻L₂ Sp) (inj₁ () ∷ In1) In2
spine-and-notand-absurd All (∧⁻L₂ Sp) (inj₂ () ∷ In1) In2


spinel-and-notand-absurd (focL-step {A} pf In Sp) In₁ A₁ with lookup In₁ In
spinel-and-notand-absurd (focL-step pf In Sp) In₁ A₁ | inj₁ refl =  
  spinel-and-notand-absurd Sp In₁ (inj₁ refl ∷ A₁) 
spinel-and-notand-absurd (focL-step pf In Sp) In₁ A₁ | inj₂ (inj₁ refl) = 
  spinel-and-notand-absurd Sp In₁ (inj₂ refl ∷ A₁) 
spinel-and-notand-absurd (focL-step pf In Sp) In₁ A₁ | inj₂ (inj₂ (inj₁ ()))
spinel-and-notand-absurd (focL-step pf In Sp) In₁ A₁ | inj₂ (inj₂ (inj₂ ()))
spinel-and-notand-absurd (focL-end pf Sp) In A = 
  spine-and-notand-absurd In Sp A [] 


----
----




{- *************
 IMPOSSIBILITIES 
-}




-- [weak.agda] weak+-spine-counterex : ∀{Γ Q X} → Spine Γ (a Q ⁻ ∷ []) (X ∷ []) (Susp (a Q ⁻)) → ⊥

-- The following is not true, due to the case where L- = a Q ⁻ 
-- spine-η⁺-adm :  ∀{Γ L- L+ U Q} → Spine (HSusp (a Q ⁺) ∷ Γ) L- L+  U → Spine Γ L- (a Q ⁺ ∷ L+) U

spine-⊥-notadm : ∀{Γ Q L- L+ U} → stable U →  Spine Γ (a Q ⁻ ∷ L-) (⊥⁺ ∷ L+) U → ⊥
spine-⊥-notadm pf ()


init-not-empty : ∀{Γ x Q L+ LA U} → Spine Γ (x ∷ a Q ⁻ ∷ LA) L+ U → ⊥
init-not-empty {L+ = []} (↑L-cons pf ())
init-not-empty {L+ = x ∷ L+} (↑L-cons pf ())
init-not-empty (⊃L V Sp) = init-not-empty Sp
init-not-empty (∧⁻L₁ Sp) = init-not-empty Sp
init-not-empty (∧⁻L₂ Sp) = init-not-empty Sp


{- NOT TRUE, DUE TO THE FOLLOWING REASON
ahmm : ∀{Γ' Γ A B U L- } 
  → Spine-l (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) L- U 
  → Spine-l (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ)  L- U 
-}

spinel-and-notand-example-absurd : ∀{Q R} 
  → Spine-l [ Pers (↑ ((a Q ⁺) ∧⁺ (a R ⁺))) ] []  (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺))) 
  → Spine-l (Pers (↑ (a Q ⁺)) ∷ [ Pers (↑ (a R ⁺)) ]) [] (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺))) 
  → ⊥
spinel-and-notand-example-absurd Sp1 Sp2 = 
  spinel-and-notand-absurd Sp2 (inj₁ refl ∷ inj₂ (inj₁ refl) ∷ []) []  

