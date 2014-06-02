open import Data.List
open import Data.Sum
open import Data.List.All
open import Data.List.Any
open Membership-≡
open import Data.Product
open import Relation.Binary.Core

module FocAdmissible where

open import Foc
open import FocWeak
open import FocProps
open import ListExtra
open import NatExtra


∧+-inv : ∀{Γ U Ω A B} → Term Γ (A ∧⁺ B ∷ Ω) U → Term Γ (A ∷ B ∷ Ω) U
∧+-inv (∧⁺L N) = N

∨+l-inv : ∀{Γ U Ω A B} → Term Γ (A ∨ B ∷ Ω) U → Term Γ (A ∷ Ω) U
∨+l-inv (∨L N₁ N₂) = N₁

∨+r-inv : ∀{Γ U Ω A B} → Term Γ (A ∨ B ∷ Ω) U → Term Γ (B ∷ Ω) U
∨+r-inv (∨L N₁ N₂) = N₂

⊤+-inv : ∀{Γ U Ω} → Term Γ (⊤⁺ ∷ Ω) U → Term Γ Ω U
⊤+-inv (⊤⁺L N) = N

↓-inv : ∀{Γ A U Ω} → Term Γ (↓ A ∷ Ω) U → Term (Pers A ∷ Γ) Ω U
↓-inv (↓L N) = N

η+-inv : ∀{Γ Q U Ω} → Term Γ (a Q ⁺ ∷ Ω) U → Term (HSusp (a Q ⁺) ∷ Γ) Ω U
η+-inv (η⁺ N) = N



∧+-inv-all : ∀{Γ Ω A B} 
  → (L : List (Type ⁻))
  → All (\x → Term Γ (A ∧⁺ B ∷ Ω) (Susp x)) L
  → All (\x → Term Γ (A ∷ B ∷ Ω) (Susp x)) L
∧+-inv-all [] Ts = []
∧+-inv-all (x ∷ xs) (px ∷ Ts) = (∧+-inv px) ∷ (∧+-inv-all xs Ts)

⊤+-inv-all : ∀{Γ Ω} 
  → (L : List (Type ⁻))
  → All (\x → Term Γ (⊤⁺ ∷ Ω) (Susp x)) L
  → All (\x → Term Γ (Ω) (Susp x)) L
⊤+-inv-all [] Ts = []
⊤+-inv-all (x ∷ xs) (px ∷ Ts) = (⊤+-inv px) ∷ (⊤+-inv-all xs Ts)

∨+l-inv-all : ∀{Γ A B Ω} 
  → (L : List (Type ⁻))
  → All (\x → Term Γ (A ∨ B ∷ Ω) (Susp x)) L
  → All (\x → Term Γ (A ∷ Ω) (Susp x)) L
∨+l-inv-all [] Ts = []
∨+l-inv-all (x ∷ xs) (px ∷ Ts) = (∨+l-inv px) ∷ (∨+l-inv-all xs Ts)

∨+r-inv-all : ∀{Γ A B Ω} 
  → (L : List (Type ⁻))
  → All (\x → Term Γ (A ∨ B ∷ Ω) (Susp x)) L
  → All (\x → Term Γ (B ∷ Ω) (Susp x)) L
∨+r-inv-all [] Ts = []
∨+r-inv-all (x ∷ xs) (px ∷ Ts) = (∨+r-inv px) ∷ (∨+r-inv-all xs Ts)

↓-inv-all : ∀{Γ A Ω} 
  → (L : List (Type ⁻))
  → All (\x → Term Γ (↓ A ∷ Ω) (Susp x)) L
  → All (\x → Term (Pers A ∷ Γ) Ω (Susp x)) L
↓-inv-all [] Ts = []
↓-inv-all (x ∷ xs) (px ∷ Ts) = (↓-inv px) ∷ (↓-inv-all xs Ts)

η+-inv-all : ∀{Γ Q Ω} 
  → (L : List (Type ⁻))
  → All (\x → Term Γ (a Q ⁺ ∷ Ω) (Susp x)) L
  → All (\x → Term (HSusp (a Q ⁺) ∷ Γ) Ω (Susp x)) L
η+-inv-all [] Ts = []
η+-inv-all (x ∷ xs) (px ∷ Ts) = (η+-inv px) ∷ (η+-inv-all xs Ts)



-----------
-----------

term-∧⁺-adm : ∀{Γ L1 L2 A B U} → Term Γ (L1 ++ A ∷ B ∷ L2) U → Term Γ (L1 ++ A ∧⁺ B ∷ L2) U
term-∧⁺-adm {L1 = []} T = ∧⁺L T
term-∧⁺-adm {L1 = ._ ∷ L1} (η⁺ N) = η⁺ (term-∧⁺-adm {L1 = L1} N)
term-∧⁺-adm {L1 = ._ ∷ L1} (↓L N) = ↓L (term-∧⁺-adm {L1 = L1} N)
term-∧⁺-adm {L1 = .⊥⁺ ∷ L1} ⊥L = ⊥L
term-∧⁺-adm {L1 = ._ ∷ L1} (∨L {A1} {B1} N₁ N₂) =  ∨L (term-∧⁺-adm {L1 = A1 ∷ L1} N₁) (term-∧⁺-adm {L1 = B1 ∷ L1}   N₂)
term-∧⁺-adm {L1 = .⊤⁺ ∷ L1} (⊤⁺L N) = ⊤⁺L (term-∧⁺-adm {L1 = L1} N)
term-∧⁺-adm {L1 = ._ ∷ L1} (∧⁺L {A = A1} {B = B1} N) = ∧⁺L (term-∧⁺-adm {L1 = A1 ∷ B1 ∷ L1}  N)

term-∧⁺-inv : ∀{Γ L1 L2 A B U} → Term Γ (L1 ++ A ∧⁺ B ∷ L2) U → Term Γ (L1 ++ A ∷ B ∷ L2) U
term-∧⁺-inv {L1 = []} (∧⁺L N) = N
term-∧⁺-inv {L1 = ._ ∷ L1} (η⁺ N) = η⁺ (term-∧⁺-inv {L1 = L1} N)
term-∧⁺-inv {L1 = ._ ∷ L1} (↓L N) = ↓L (term-∧⁺-inv {L1 = L1} N)
term-∧⁺-inv {L1 = .⊥⁺ ∷ L1} ⊥L = ⊥L
term-∧⁺-inv {L1 = ._ ∷ L1} (∨L {A = A₁} {B = B₁} N₁ N₂) = 
  ∨L (term-∧⁺-inv {L1 = A₁ ∷ L1} N₁) (term-∧⁺-inv {L1 = B₁ ∷ L1} N₂) 
term-∧⁺-inv {L1 = .⊤⁺ ∷ L1} (⊤⁺L N) = ⊤⁺L (term-∧⁺-inv {L1 = L1} N)
term-∧⁺-inv {L1 = ._ ∷ L1} (∧⁺L {A = A₁} {B = B₁} N) = ∧⁺L (term-∧⁺-inv {L1 = A₁ ∷ B₁ ∷ L1} N )  


term-∨L-adm : ∀{Γ L1 L2 A B U} → Term Γ (L1 ++ A ∷ L2) U → Term Γ (L1 ++ B ∷ L2) U → Term Γ (L1 ++ A ∨ B ∷ L2) U
term-∨L-adm {L1 = []} T1 T2 = ∨L T1 T2
term-∨L-adm {L1 = ._ ∷ L1} (η⁺ N) (η⁺ N₁) = η⁺ (term-∨L-adm {L1 = L1} N N₁)
term-∨L-adm {L1 = ._ ∷ L1} (↓L N) (↓L N₁) = ↓L (term-∨L-adm {L1 = L1} N N₁)
term-∨L-adm {L1 = .⊥⁺ ∷ L1} ⊥L ⊥L = ⊥L
term-∨L-adm {L1 = ._ ∷ L1} (∨L {A₁} {B₁} N₁ N₂) (∨L N₃ N₄) = 
  ∨L (term-∨L-adm {L1 = A₁ ∷ L1} N₁ N₃) (term-∨L-adm {L1 = B₁ ∷ L1} N₂ N₄) 
term-∨L-adm {L1 = .⊤⁺ ∷ L1} (⊤⁺L N) (⊤⁺L N₁) = ⊤⁺L (term-∨L-adm {L1 = L1} N N₁)
term-∨L-adm {L1 = ._ ∷ L1} (∧⁺L {A = A₁} {B = B₁} N) (∧⁺L N₁) = ∧⁺L (term-∨L-adm {L1 = A₁ ∷ B₁ ∷ L1} N N₁) 

term-∨L-inv : ∀{Γ L1 L2 A B U} → Term Γ (L1 ++ A ∨ B ∷ L2) U →  Term Γ (L1 ++ A ∷ L2) U × Term Γ (L1 ++ B ∷ L2) U
term-∨L-inv {L1 = []} (∨L N₁ N₂) = N₁ , N₂
term-∨L-inv {L1 = ._ ∷ L1} (η⁺ N) with term-∨L-inv {L1 = L1} N 
...  | T1 , T2  = η⁺ T1 , η⁺ T2 
term-∨L-inv {L1 = ._ ∷ L1} (↓L N) with term-∨L-inv {L1 = L1} N 
... | T1 , T2  = ↓L T1 , ↓L T2
term-∨L-inv {L1 = .⊥⁺ ∷ L1} ⊥L = ⊥L , ⊥L
term-∨L-inv {L1 = ._ ∷ L1} (∨L {A₁} {B₁} N₁ N₂) with (term-∨L-inv {L1 = A₁ ∷ L1} N₁) | (term-∨L-inv {L1 = B₁ ∷ L1} N₂)
... | (T1 , T2) | (T'1 , T'2) = (∨L T1 T'1) , (∨L T2 T'2) 
term-∨L-inv {L1 = .⊤⁺ ∷ L1} (⊤⁺L N)   with term-∨L-inv {L1 = L1} N 
term-∨L-inv {Γ} {.⊤⁺ ∷ L1} (⊤⁺L N) | T1 , T2 = ⊤⁺L T1 , ⊤⁺L T2
term-∨L-inv {L1 = ._ ∷ L1} (∧⁺L {A = A₁} {B = B₁} N) 
  with term-∨L-inv {L1 = A₁ ∷ B₁ ∷ L1}  N 
term-∨L-inv {Γ} {._ ∷ L1} {L2 = L2}  (∧⁺L N) | T1 , T2 = (∧⁺L T1) , (∧⁺L T2)




term-⊥-adm : ∀{Γ L+ U} → ⊥⁺ ∈ L+ → Term Γ L+ U
term-⊥-adm (here refl) = ⊥L
term-⊥-adm (there {x} In) = weak+-term x (term-⊥-adm In)  



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




cntr-+-term-gen-helper : ∀{Γ X L+ U N } → Term Γ (X ∷ L+) U → X ∈ L+ → N >′ size-list+-formulas (X ∷ L+)  → Term Γ L+ U

cntr-+-term-gen : ∀{Γ X L+ U N } → Term Γ (X ∷ L+) U → X ∈ L+ → size-list+-formulas (X ∷ L+) ≡ N → Term Γ L+ U

cntr-+-term-gen-helper T In (>′-refl m≡n) = cntr-+-term-gen T In refl 
cntr-+-term-gen-helper T In (>′-step Ineq) = cntr-+-term-gen-helper T In Ineq 



cntr-+-term-gen (η⁺ N) In S =  {!!}
cntr-+-term-gen {L+ = []} (↓L N) () _
cntr-+-term-gen {L+ = ._ ∷ L+} (↓L N) (here refl) S = cntr-pers-term-bis N
cntr-+-term-gen {L+ = x ∷ L+} (↓L N) (there In) S = cntr-pers-term-bis-gen {Γ' = []} N (there In) 
cntr-+-term-gen ⊥L In S = term-⊥-adm In 
cntr-+-term-gen (∨L N₁ N₂) In S with in-split In
... | L1 , L2 , Eq rewrite Eq = {!!} 
cntr-+-term-gen (⊤⁺L N) In S = N
cntr-+-term-gen (∧⁺L {A = A} {B = B} N) In S with in-split In
... | L1 , L2 , Eq rewrite Eq = 
  term-∧⁺-adm {L1 = L1}
  (cntr-+-term-gen {N = {!!}}
    (cntr-+-term-gen {N = {!!}} (term-∧⁺-inv {L1 = A ∷ B ∷ L1} N) ({!!}) {!!})
    {!!} 
    {!!})


cntr-+-term : ∀{Γ X L+ N U} → Term Γ (X ∷ X ∷ L+) U → size-list+-formulas (X ∷ X ∷ L+) ≡ N → Term Γ (X ∷ L+) U
cntr-+-term (η⁺ N) S = {!!}
cntr-+-term (↓L N) S = {!!}
cntr-+-term ⊥L S = ⊥L
cntr-+-term (∨L N₁ N₂) S = {!!}
cntr-+-term (⊤⁺L N) S = N
cntr-+-term (∧⁺L N) S = {!!} --cntr-+-term (term-∧⁺-inv-adm N) {!!}  



postulate
  spine-∧⁺-adm : ∀{Γ L- L+ A B U} → Spine Γ L- (A ∷ B ∷ L+) U → Spine Γ L- (A ∧⁺ B ∷ L+) U





{-
 TODO: Prove/ HARD!! -}
spine-∨-adm : ∀{Γ L- L+ A B U} 
    → Spine Γ L- (A ∷ L+) U 
    → Spine Γ L- (B ∷ L+) U 
    → Spine Γ L- (A ∨ B ∷ L+) U


spine-∨-adm' : ∀{Γ L- L+ L'+ A B U}
  → stable U
  → Spine Γ L- (A ∷ L+) U 
  → Spine Γ L- (B ∷ L'+) U 
  → Spine Γ L- (A ∨ B ∷ L+ ++ L'+) U

spine-∨-adm' pf (↑L-cons pf₁ N) (↑L-cons pf₂ N₁) = ↑L-cons pf₂ (spine-∨-adm' pf₂ {!!} {!!}) --Weak spine + 
spine-∨-adm' pf (↑L-nil pf₁ N) (↑L-nil pf₂ N₁) =  ↑L-nil pf₁ (∨L {!!} {!!} ) -- weak term +
spine-∨-adm' pf (⊃L V Sp) (⊃L V₁ Sp₁) =  ⊃L V (spine-∨-adm' pf {!!} {!!} )  --Weak spine + 
spine-∨-adm' pf (∧⁻L₁ Sp) (∧⁻L₁ Sp₁) = ∧⁻L₁ (spine-∨-adm' pf Sp Sp₁ ) 
spine-∨-adm' pf (∧⁻L₁ {C} {D}  Sp) (∧⁻L₂  Sp₁) with spine-possib-phases Sp
spine-∨-adm' pf (∧⁻L₁ {C} {D} Sp) (∧⁻L₂ Sp₁) | inj₁ (refl , ())
spine-∨-adm' pf (∧⁻L₁ {C} {D}  Sp) (∧⁻L₂ Sp₁) | inj₂ (L++ , Exp , H) with spine-possib-phases Sp₁
spine-∨-adm' pf (∧⁻L₁ {C} {D} Sp) (∧⁻L₂ Sp₁) | inj₂ (L++ , Exp , H) | inj₁ (proj₁ , ())
spine-∨-adm' pf (∧⁻L₁ {C} {D} Sp) (∧⁻L₂ Sp₁) | inj₂ (L++ , Exp , H) | inj₂ (L++' , Exp' , H') = 
  {!∧⁻L₂ {A = C} (H' pf (spine-∨-adm' pf Exp Exp'))!} 

spine-∨-adm' pf (∧⁻L₂ Sp) (∧⁻L₁ Sp₁) = {!!}
spine-∨-adm' pf (∧⁻L₂ Sp) (∧⁻L₂ Sp₁) = ∧⁻L₂ (spine-∨-adm' pf Sp Sp₁ ) 


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

spine-∧⁻-adm : ∀{Γ L- L+ A B U} → Spine Γ (A ∷ B ∷ L-) L+ U → Spine Γ (A ∧⁻ B ∷ L-) L+ U
spine-∧⁻-adm {A = A} {B = B} Sp = {!∧⁻L₁ (spine-∧⁻L₂-adm {L' = [ A ]} Sp) !} 


  
postulate 
  spine-↑-adm : ∀{Γ L- L1 L2 A U} → Spine Γ L- ((L1 ++ [ A ]) ++ L2) U → Spine Γ (↑ A ∷ L-) (L1 ++ L2) U

-- The following is NOT admissible, if L- is an atom
-- spine-⊤⁺-adm :  ∀{Γ L- L+ U} → Spine Γ L- L+  U → Spine Γ L- (⊤⁺ ∷ L+) U