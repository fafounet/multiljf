open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open import Data.Product
open import Data.Unit
open import Data.Bool renaming (_∨_ to _or_)
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


load-std : ∀{Γ U} → Spine-l Γ [] U → Term Γ [] U
load-std (focL-step pf In Sp) = focL-init pf (focL-step pf In Sp)
load-std (focL-end pf Sp) = focL-init pf (focL-end pf Sp)




∧-residual-loading : ∀{Γ A B L1 L2 U} → 
 Spine-l (Γ) (L1 ++ A ∧⁻ B ∷ L2) U → 
 Spine-l (Γ) (L1 ++ A ∷ B ∷ L2) U 
∧-residual-loading {L1 = []} (focL-step pf In Sp) = {!!}
∧-residual-loading {L1 = []} (focL-end pf id⁻) = {!!}
∧-residual-loading {L1 = []} (focL-end pf (∧⁻L₁ Sp)) = {!!}
∧-residual-loading {L1 = []} (focL-end pf (∧⁻L₂ Sp)) = {!!}
∧-residual-loading {L1 = x ∷ L1} Sp = {!!}

load-inv-step-adm : ∀{Γ1 Γ2 X L U} 
  → stable U 
  → Spine-l (Γ1 ++ Pers X ∷ Γ2) (X ∷ L) U 
  → Spine-l (Γ1 ++ Pers X ∷ Γ2) (L) U
load-inv-step-adm {Γ1} {X = X} pf Sp = focL-step pf (in-append-in {X = Pers X} {L1 = Γ1})  Sp


∧-context-adm : ∀{Γ1 Γ2 A B L} 
  → Exp (Γ1 ++ Pers (A ∧⁻ B) ∷ Γ2)  L 
  → Exp (Γ1 ++ Pers A ∷ Pers B ∷ Γ2)  L

∧-context-loading-adm : ∀{Γ1 Γ2 A B L} 
  → Exp-l (Γ1 ++ Pers (A ∧⁻ B) ∷ Γ2)  L 
  → Exp-l (Γ1 ++ Pers A ∷ Pers B ∷ Γ2)  L

∧-context-loading-adm {Γ1} (focL-step pf In Sp) with fromctx Γ1 In
∧-context-loading-adm {Γ1} {Γ2} {A} {B} (focL-step pf In Sp) | inj₁ refl 
  = {!!}
... | inj₂ X = {!!} --focL-step pf {!!} (∧-context-loading-adm Sp)
∧-context-loading-adm {Γ1} (focL-end pf Sp) = focL-end pf (∧-context-adm {Γ1} Sp)


∧-context-adm {Γ1} (id⁺ v) with fromctx Γ1 v 
∧-context-adm (id⁺ v) | inj₁ ()
... | inj₂ X = id⁺ (in-append-double-weak {L1 = Γ1} X)
∧-context-adm {Γ1} (↓R N) = ↓R (∧-context-adm {Γ1} N)
∧-context-adm {Γ1}  (∨R₁ V) = ∨R₁ (∧-context-adm {Γ1}  V)
∧-context-adm {Γ1}  (∨R₂ V) = ∨R₂ (∧-context-adm {Γ1}  V)
∧-context-adm {Γ1}  ⊤⁺R = ⊤⁺R
∧-context-adm {Γ1}  (∧⁺R V₁ V₂) = ∧⁺R (∧-context-adm {Γ1}  V₁) (∧-context-adm {Γ1}  V₂)
∧-context-adm {Γ1}  (focR V) = focR (∧-context-adm {Γ1}  V)
∧-context-adm {Γ1} {Γ2} {A = A} {B = B} (focL-init pf Sp) 
  = load-std {Γ = Γ1 ++ Pers A ∷ Pers B ∷ Γ2} (∧-context-loading-adm {Γ1} {Γ2} {A = A} {B = B} Sp)
∧-context-adm {Γ1}  (η⁺ {Q} N) = η⁺ (∧-context-adm {Γ1 = HSusp (a Q ⁺) ∷ Γ1}  N)
∧-context-adm {Γ1}  (↓L {A₁} N) = ↓L (∧-context-adm {Γ1 = Pers A₁ ∷ Γ1}  N)
∧-context-adm {Γ1}  ⊥L = ⊥L
∧-context-adm {Γ1}  (∨L N₁ N₂) = ∨L (∧-context-adm {Γ1}  N₁) (∧-context-adm {Γ1}  N₂)
∧-context-adm {Γ1}  (⊤⁺L N) = ⊤⁺L (∧-context-adm {Γ1}  N)
∧-context-adm {Γ1}  (∧⁺L N) = ∧⁺L (∧-context-adm {Γ1}  N)
∧-context-adm {Γ1}  (η⁻ N) = η⁻ (∧-context-adm {Γ1}  N)
∧-context-adm {Γ1}  (↑R N) = ↑R (∧-context-adm {Γ1}  N)
∧-context-adm {Γ1}  (⊃R N) = ⊃R (∧-context-adm {Γ1}  N)
∧-context-adm {Γ1}  ⊤⁻R = ⊤⁻R
∧-context-adm {Γ1}  (∧⁻R N₁ N₂) = ∧⁻R (∧-context-adm {Γ1}  N₁) (∧-context-adm {Γ1}  N₂)
∧-context-adm {Γ1}  id⁻ = id⁻
∧-context-adm {Γ1}  (↑L-cons pf N) = ↑L-cons pf (∧-context-adm {Γ1}  N)
∧-context-adm {Γ1}  (↑L-nil pf N) = ↑L-nil pf (∧-context-adm {Γ1}  N)
∧-context-adm {Γ1}  (⊃L V Sp) = ⊃L (∧-context-adm {Γ1}  V) (∧-context-adm {Γ1}  Sp)
∧-context-adm {Γ1}  (∧⁻L₁ Sp) = ∧⁻L₁ (∧-context-adm {Γ1}  Sp)
∧-context-adm {Γ1}  (∧⁻L₂ Sp) = ∧⁻L₂ (∧-context-adm {Γ1}  Sp)


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


unload-all-term : ∀{Γ U} 
  → (L : List (Type ⁻)) 
  → (pf : stable U) 
  → Spine Γ L [] U 
  → Data.List.map Pers L ⊆ Γ 
  → Term Γ [] U 
unload-all-term L- pf Sp In = focL-init pf (unload-all-l L-  pf (focL-end pf Sp) In) 

unload-one-adm : ∀{Γ X Y L- L+ U} 
  → (pf : stable U) 
  → Spine Γ (Y ∷ L-) (X ∷ L+) U 
  → Data.List.map Pers (Y ∷ L-) ⊆ Γ 
  → Spine Γ L- (X ∷ L+) U 
unload-one-adm {Y = a Q .⁻} pf () Sub
unload-one-adm {Y = ↑ x} {[]} pf (↑L-cons pf₁ N) Sub = {!!}
unload-one-adm {Y = ↑ x} {x₁ ∷ L-} pf (↑L-cons pf₁ N) Sub = {!!}
unload-one-adm {Y = A ⊃ B} pf (⊃L V Sp) Sub = {!!}
unload-one-adm {Y = ⊤⁻} pf () Sub
unload-one-adm {Y = A ∧⁻ Y₁} pf (∧⁻L₁ Sp) Sub = {!!}
unload-one-adm {Y = A ∧⁻ Y₁} pf (∧⁻L₂ Sp) Sub = {!!}

unload-all-adm-bis : ∀{Γ X L- L+ U} 
  → (pf : stable U) 
  → Spine Γ L- (X ∷ L+) U 
  → Data.List.map Pers L- ⊆ Γ 
  → Spine Γ [] (X ∷ L+) U 
unload-all-adm-bis {X = a Q .⁺} {L+ = []} pf (↑L-cons pf₁ N) Sub = {!unload-all-adm-bis pf N ?!}
unload-all-adm-bis {X = a Q .⁺} {L+ = []} pf (↑L-nil pf₁ N) Sub = {!!}
unload-all-adm-bis {X = a Q .⁺} {L+ = []} pf (⊃L V Sp) Sub = {!!}
unload-all-adm-bis {X = a Q .⁺} {L+ = []} pf (∧⁻L₁ Sp) Sub = {!!}
unload-all-adm-bis {X = a Q .⁺} {L+ = []} pf (∧⁻L₂ Sp) Sub = {!!}
unload-all-adm-bis {X = ↓ X} {L+ = []} pf Sp Sub = {!!}
unload-all-adm-bis {X = ⊥⁺} {L+ = []} pf Sp Sub = {!!}
unload-all-adm-bis {X = X ∨ X₁} {L+ = []} pf Sp Sub = {!!}
unload-all-adm-bis {X = ⊤⁺} {L+ = []} pf Sp Sub = {!!}
unload-all-adm-bis {X = X ∧⁺ X₁} {L+ = []} pf Sp Sub = {!!}
unload-all-adm-bis {L+ = x ∷ L+} pf Sp Sub = {!!}





unload-all-adm : ∀{Γ X L- L+ U} 
  → (pf : stable U) 
  → Spine Γ L- (X ∷ L+) U 
  → Data.List.map Pers L- ⊆ Γ 
  → Spine Γ [] (X ∷ L+) U 
unload-all-adm {L- = []} pf Sp Sub = Sp
unload-all-adm {L- = x ∷ L-} pf Sp Sub = unload-all-adm pf (unload-one-adm pf Sp Sub) (λ {x₁} z → Sub (there z))


spine-init : ∀{Γ Q LA U L+}
  → Spine Γ (a Q ⁻ ∷ LA) L+ U 
  → ((LA ≡ []) × (L+ ≡ []))
spine-init id⁻ = refl , refl


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




{-has-atomic-residual : Type ⁻ → Bool
has-atomic-residual (a Q .⁻) = true
has-atomic-residual (↑ x) = {!!}
has-atomic-residual (x ⊃ x₁) = {!!}
has-atomic-residual ⊤⁻ = false
has-atomic-residual (x ∧⁻ x₁) = {!!} --has-atomic-residual x  || has-atomic-residual x₁
-}

{-
spine-⊥ : ∀{Γ L- L+ U} → stable U →  (Spine Γ L- (⊥⁺ ∷ L+) U ⊎ ∃ λ Q → (a Q ⁻ ∈ L-))
spine-⊥ {L- = []} pf = inj₁ (↑L-nil pf ⊥L)
spine-⊥ {L- = a Q .⁻ ∷ L- } pf = inj₂ (Q , here refl)
spine-⊥ {L- = ↑ x ∷ L- } pf = {!!}
spine-⊥ {L- = x ⊃ x₁ ∷ L- } pf = {!!}
spine-⊥ {L- = ⊤⁻ ∷ L- } pf = {!!}
spine-⊥ {Γ} {x ∧⁻ x₁ ∷ L- } {L+} {U} pf with spine-⊥ {Γ} {L- } {L+} {U} pf  
spine-⊥ {Γ} {x₁ ∧⁻ x₂ ∷ L- } pf | inj₁ x = {!inj!}
spine-⊥ {Γ} {x ∧⁻ x₁ ∷ L- } pf | inj₂ y = {!!}

-}






spine-[]-[] : ∀{Γ U} → Spine Γ [] [] U → ⊥
spine-[]-[]  = λ {Γ} {U} → λ ()

term-[]-⊤ : ∀{Γ} → Term Γ [] (True ⊤⁺)
term-[]-⊤ = λ {Γ} → focR ⊤⁺R

term-⊤ : ∀{Γ} → (L+ : (List (Type ⁺))) → Term Γ L+ (True ⊤⁺) 
term-⊤ [] = focR ⊤⁺R
term-⊤ (x ∷ L+) = weak+-term x (term-⊤ L+)


spine-[]-⊤ : ∀{Γ L+} → (X : Type ⁺) → Spine Γ [] (X ∷ L+) (True ⊤⁺)
spine-[]-⊤ {L+ = L+} X = ↑L-nil tt (term-⊤ (X ∷ L+))







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



{- *************
 IMPOSSIBILITIES 
-}




{- This is not true, due to the following counter example 
subst-term-[] : ∀{Γ x LA U L+} → Term Γ [] (Susp x) → Spine Γ (x ∷ LA) L+ U → Spine Γ LA L+ U -}
cex : ∀{Q} → Term [] [] (Susp (a Q ⁻)) → Spine [] [] [] (Susp (a Q ⁻)) → ⊥
cex (focL-init pf (focL-step pf₁ In Sp)) = λ ()
cex (focL-init pf (focL-end pf₁ ()))


{-
spine-⊤ : ∀{Γ} → (L- : List (Type ⁻)) → (L+ : List (Type ⁺)) → Spine Γ L- L+ (True ⊤⁺)
spine-⊤ = {!!}
 Not true due to the following case, unrelated to multifocusing: -}
counter-ex : ∀{Q} → Spine [] [ a Q ⁻ ] [] (True ⊤⁺) → ⊥ 
counter-ex () 



spine-append-neg-lit-absurd : ∀{Γ L- L+ Q X U} → Spine Γ (a Q ⁻ ∷ L-) (L+ ++ [ X ]) U → ⊥
spine-append-neg-lit-absurd {L+ = []} ()
spine-append-neg-lit-absurd {L+ = x ∷ L+} ()


spine-cons-neg-lit-absurd : ∀{Γ X L- L+ Q U} → Spine Γ (X ∷ L-) L+ U → (a Q ⁻ ∈ L-) → ⊥ 
spine-cons-neg-lit-absurd {X = a Q .⁻} id⁻ ()
spine-cons-neg-lit-absurd {X = ↑ X} id⁻ ()
spine-cons-neg-lit-absurd {X = ↑ x} {[]} (↑L-cons pf N) ()
spine-cons-neg-lit-absurd {X = ↑ x} {._ ∷ L-} {L+} (↑L-cons pf N) (here refl) 
  = spine-append-neg-lit-absurd {L+ = L+} N
spine-cons-neg-lit-absurd {X = ↑ x} {x₁ ∷ L-} (↑L-cons pf N) (there In) = spine-cons-neg-lit-absurd N In
spine-cons-neg-lit-absurd {X = X ⊃ X₁} id⁻ ()
spine-cons-neg-lit-absurd {X = A ⊃ B} (⊃L V Sp) In =  spine-cons-neg-lit-absurd Sp In
spine-cons-neg-lit-absurd {X = ⊤⁻} id⁻ ()
spine-cons-neg-lit-absurd {X = X ∧⁻ X₁} id⁻ ()
spine-cons-neg-lit-absurd {X = A ∧⁻ X₁} (∧⁻L₁ Sp) In = spine-cons-neg-lit-absurd Sp In
spine-cons-neg-lit-absurd {X = A ∧⁻ X₁} (∧⁻L₂ Sp) In = spine-cons-neg-lit-absurd Sp In 