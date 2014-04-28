open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open import Data.Product
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.List
open import Data.List.All
open import Data.List.Any
open Membership-≡

open import Foc
open import Weak
open import NatExtra
open import ListExtra
open import Subset

module FocProps where


loading-done : ∀{Γ L U}
  → (s : Spine-l Γ L U)
  → ∃ λ L' →  (Data.List.map Pers L') ⊆ Γ ×
    Σ (Spine Γ (L' ++ L) [] U)  (\s' → height-l s >′ height s')


loading-done {L = L} (focL-step {A = A} pf In Sp)  with loading-done Sp 
loading-done {L = L} (focL-step {A = A} pf In Sp) | [] , Sub , Sp' , IEq = 
  (A ∷ []) , (in-sing-sub In , (Sp' , >′-step IEq))
loading-done {L = L} (focL-step {A = A} pf In Sp) | x ∷ C , Sub , Sp' , IEq 
  rewrite cons-nil-cons-concat {x = x} {C = C} {A = A} {L = L}  = 
     x ∷ C ++ A ∷ [] , (cons-sub-in-append Sub In , (Sp' , >′-step IEq))
loading-done {Γ} (focL-end pf Sp) = [] , (λ {x} → λ ()) ,  Sp , >′-refl refl 

unload-all-l : ∀{Γ U} → (L : List (Type ⁻)) → (pf : stable U) → Spine-l Γ L U → Data.List.map Pers L ⊆ Γ → Spine-l Γ [] U 
unload-all-l [] pf Sp In = Sp
unload-all-l (x ∷ L) pf Sp In = unload-all-l L pf (focL-step pf (In (here refl)) Sp) (λ {x₁} z → In (there z))


unload-all : ∀{Γ U} 
  → (L : List (Type ⁻)) 
  → (pf : stable U) 
  → Spine Γ L [] U 
  → Data.List.map Pers L ⊆ Γ 
  → Term Γ [] U 
unload-all L- pf Sp In = focL-init pf (unload-all-l L-  pf (focL-end pf Sp) In) 

{- Not precise enough for many purposes -}
postulate 
  spine-to-term : ∀{Γ X L- L+ U}
    → (s : Spine Γ L- (X ∷ L+) U)
    → (∃ λ L' → 
      (Term Γ (X ∷ (L+ ++ L')) U) )



{-
{- There are two possible ways to end a spine phase:
- either we are done with this subtree (the case where LA = L+ = [])
- or we cannot be done, and we will have to end it, and start a new one later
-}
spine-possib-phases : ∀{Γ LA U L+}
  → (A : Type ⁻)
  → Spine Γ (A ∷ LA) L+ U 
  → ((LA ≡ []) × (L+ ≡ []))
         ⊎
  (∃ λ RA → 
    ∃ λ LIG → 
     (Spine Γ LA (L+ ++ RA) U) × 
     -- Don't forget the Left Implications Parts to reconstruct!
     (All (\x → Value Γ x) LIG) ×
       -- It's important to be able to reconstruct the negative multifocused part
       -- for ANY spine, 
       (∀{LA' L'+ U'} → stable U' → Spine Γ LA' (L'+ ++ RA) U' →  Spine Γ (A ∷ LA') L'+ U'))
spine-possib-phases (a Q .⁻) id⁻ = inj₁ (refl , refl)
spine-possib-phases (↑ A) id⁻ = inj₁ (refl , refl)
spine-possib-phases {Γ} {[]} {U} {L+} (↑ x) (↑L-cons pf N) = 
  inj₂ (x ∷ [] , ([] , (N , ([] , (λ x₁ x₂ → ↑L-cons x₁ x₂)))))
spine-possib-phases {Γ} {x ∷ LA} (↑ x₁) (↑L-cons pf N) with spine-possib-phases _ N
spine-possib-phases {Γ} {x ∷ LA} (↑ x₁) (↑L-cons pf N) | inj₁ x₂ = inj₂ (x₁ ∷ [] , [] , N , [] , ↑L-cons)
spine-possib-phases {Γ} {x ∷ LA} (↑ x₁) (↑L-cons pf N) | inj₂ y = inj₂ (x₁ ∷ [] , [] , N , [] , ↑L-cons)

spine-possib-phases (A ⊃ A₁) id⁻ = inj₁ (refl , refl)
spine-possib-phases (A ⊃ B) (⊃L V Sp) with spine-possib-phases B Sp
spine-possib-phases (A ⊃ B) (⊃L V Sp) | inj₁ x = inj₁ x
spine-possib-phases (A ⊃ B) (⊃L V Sp) | inj₂ (RA , LIG , Sp' , LV , R)  = 
  inj₂ (RA , LIG , Sp' , LV , (λ {x₁} {x₂} {x₃} pf x₄  → ⊃L V (R pf x₄)))

spine-possib-phases ⊤⁻ id⁻ = inj₁ (refl , refl)
spine-possib-phases (A ∧⁻ A₁) id⁻ = inj₁ (refl , refl)
spine-possib-phases (A ∧⁻ A₁) (∧⁻L₁ Sp) with spine-possib-phases A Sp
spine-possib-phases (A ∧⁻ A₁) (∧⁻L₁ Sp) | inj₁ x = inj₁ x
spine-possib-phases (A ∧⁻ A₁) (∧⁻L₁ Sp) | inj₂ (RA , LIG , Sp' , LV , R) = 
  inj₂ (RA , LIG , Sp' , LV , (λ {x₁} {x₂} {x₃} pf x₄ → ∧⁻L₁ (R pf x₄)))
spine-possib-phases (A ∧⁻ A₁) (∧⁻L₂ Sp) with spine-possib-phases A₁ Sp
spine-possib-phases (A ∧⁻ A₁) (∧⁻L₂ Sp) | inj₁ x = inj₁ x
spine-possib-phases (A ∧⁻ A₁) (∧⁻L₂ Sp) | inj₂ (RA , LIG , Sp' , LV , R) = 
  inj₂ (RA , LIG , Sp' , LV , (λ {x₁} {x₂} {x₃} pf x₄ → ∧⁻L₂ (R pf x₄)))
-}  


spine-possib-phases : ∀{Γ LA U L+}
  → (A : Type ⁻)
  → Spine Γ (A ∷ LA) L+ U 
  → ((LA ≡ []) × (L+ ≡ []))
         ⊎
  (∃ λ RA → 
     (Spine Γ LA (L+ ++ RA) U) × 
      -- It's important to be able to reconstruct the negative multifocused part
      -- for ANY spine, 
       (∀{LA' L'+ U'} → stable U' → Spine Γ LA' (L'+ ++ RA) U' →  Spine Γ (A ∷ LA') L'+ U'))
spine-possib-phases (a Q .⁻) id⁻ = inj₁ (refl , refl)
spine-possib-phases (↑ A) id⁻ = inj₁ (refl , refl)
spine-possib-phases {Γ} {[]} {U} {L+} (↑ x) (↑L-cons pf N) = 
  inj₂ (x ∷ [] , N , ↑L-cons)
spine-possib-phases {Γ} {x ∷ LA} (↑ x₁) (↑L-cons pf N) with spine-possib-phases _ N
spine-possib-phases {Γ} {x ∷ LA} (↑ x₁) (↑L-cons pf N) | inj₁ x₂ = inj₂ (x₁ ∷ [] , N , ↑L-cons)
spine-possib-phases {Γ} {x ∷ LA} (↑ x₁) (↑L-cons pf N) | inj₂ y = inj₂ (x₁ ∷ [] , N , ↑L-cons)

spine-possib-phases (A ⊃ A₁) id⁻ = inj₁ (refl , refl)
spine-possib-phases (A ⊃ B) (⊃L V Sp) with spine-possib-phases B Sp
spine-possib-phases (A ⊃ B) (⊃L V Sp) | inj₁ x = inj₁ x
spine-possib-phases (A ⊃ B) (⊃L V Sp) | inj₂ (RA  , Sp' , R)  = 
  inj₂ (RA , Sp' , (λ {x₁} {x₂} {x₃} pf x₄  → ⊃L V (R pf x₄)))

spine-possib-phases ⊤⁻ id⁻ = inj₁ (refl , refl)
spine-possib-phases (A ∧⁻ A₁) id⁻ = inj₁ (refl , refl)
spine-possib-phases (A ∧⁻ A₁) (∧⁻L₁ Sp) with spine-possib-phases A Sp
spine-possib-phases (A ∧⁻ A₁) (∧⁻L₁ Sp) | inj₁ x = inj₁ x
spine-possib-phases (A ∧⁻ A₁) (∧⁻L₁ Sp) | inj₂ (RA , Sp' , R) = 
  inj₂ (RA  , Sp' , (λ {x₁} {x₂} {x₃} pf x₄ → ∧⁻L₁ (R pf x₄)))
spine-possib-phases (A ∧⁻ A₁) (∧⁻L₂ Sp) with spine-possib-phases A₁ Sp
spine-possib-phases (A ∧⁻ A₁) (∧⁻L₂ Sp) | inj₁ x = inj₁ x
spine-possib-phases (A ∧⁻ A₁) (∧⁻L₂ Sp) | inj₂ (RA , Sp' , R) = 
  inj₂ (RA , Sp' , (λ {x₁} {x₂} {x₃} pf x₄ → ∧⁻L₂ (R pf x₄)))




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

postulate
  spine-∨-adm : ∀{Γ L- L+ A B U} → Spine Γ L- (A ∷ L+) U → Spine Γ L- (B ∷ L+) U → Spine Γ L- (A ∨ B ∷ L+) U
  
postulate 
  spine-↑-adm : ∀{Γ L- L1 L2 A U} → Spine Γ L- ((L1 ++ [ A ]) ++ L2) U → Spine Γ (↑ A ∷ L-) (L1 ++ L2) U

postulate
  spine-⊤⁺-adm :  ∀{Γ L- L+ U} → Spine Γ L- L+  U → Spine Γ L- (⊤⁺ ∷ L+) U



spine-[]-[] : ∀{Γ U} → Spine Γ [] [] U → ⊥
spine-[]-[]  = λ {Γ} {U} → λ ()

term-[]-⊤ : ∀{Γ} → Term Γ [] (True ⊤⁺)
term-[]-⊤ = λ {Γ} → focR ⊤⁺R

term-⊤ : ∀{Γ} → (L+ : (List (Type ⁺))) → Term Γ L+ (True ⊤⁺) 
term-⊤ [] = focR ⊤⁺R
term-⊤ (x ∷ L+) = weak+-term x (term-⊤ L+)


spine-[]-⊤ : ∀{Γ L+} → (X : Type ⁺) → Spine Γ [] (X ∷ L+) (True ⊤⁺)
spine-[]-⊤ {L+ = L+} X = ↑L-nil tt (term-⊤ (X ∷ L+))


{-
spine-⊤ : ∀{Γ} → (L- : List (Type ⁻)) → (L+ : List (Type ⁺)) → Spine Γ L- L+ (True ⊤⁺)
spine-⊤ = {!!}
 Not true due to the following case, unrelated to multifocusing: -}
counter-ex : ∀{Q} → Spine [] [ a Q ⁻ ] [] (True ⊤⁺) → ⊥ 
counter-ex () 




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

