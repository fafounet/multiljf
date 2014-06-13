open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open import Data.Product
open import Data.Unit
open import Data.Bool renaming (_∨_ to _or_)
open import Data.Sum 
open import Data.Nat hiding (_≤′_; module _≤′_; _<′_; _≥′_; _>′_)

open import Data.Product
open import Data.Empty
open import Data.List
open import Data.List.All
open import Data.List.Any
open Membership-≡
open import Function

open import Foc
open import FocWeak
open import FocSimpleCntr

open import NatExtra
open import ListExtra
open import Subset

module FocProps where


load-std : ∀{Γ U} → Spine-l Γ [] U → Term Γ [] U
load-std (focL-step pf In Sp) = focL-init pf (focL-step pf In Sp)
load-std (focL-end pf Sp) = focL-init pf (focL-end pf Sp)


unload-all-l : ∀{Γ U} → (L : List (Type ⁻)) → (pf : stable U) → Spine-l Γ L U → Data.List.map Pers L ⊆ Γ → Spine-l Γ [] U 
unload-all-l [] pf Sp In = Sp
unload-all-l (x ∷ L) pf Sp In = unload-all-l L pf (focL-step pf (In (here refl)) Sp) (λ {x₁} z → In (there z))


unload-partial-l : ∀{Γ L2 U} 
  → (L1 : List (Type ⁻)) 
  → (pf : stable U) 
  → Spine-l Γ (L1 ++ L2) U 
  → Data.List.map Pers L1 ⊆ Γ 
  → Spine-l Γ L2 U 
unload-partial-l [] pf Sp In = Sp
unload-partial-l (x ∷ L) pf Sp In = unload-partial-l L pf (focL-step pf (In (here refl)) Sp)
                                      (λ {x₁} z → In (there z))



load-inv-step-adm : ∀{Γ1 Γ2 X L U} 
  → stable U 
  → Spine-l (Γ1 ++ Pers X ∷ Γ2) (X ∷ L) U 
  → Spine-l (Γ1 ++ Pers X ∷ Γ2) (L) U
load-inv-step-adm {Γ1} {X = X} pf Sp = focL-step pf (in-append-cons {X = Pers X} {L1 = Γ1})  Sp

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


loading-done-unprecise : ∀{Γ L- U}
  → Spine-l Γ L- U 
  → 
  (∃ λ L' → 
    ((Data.List.map Pers L') ⊆ Γ)
    × Spine Γ (L' ++ L-) [] U)
loading-done-unprecise Sp  with loading-done Sp 
... | L' , Sub , Sp' , _ = L' , Sub , Sp' 



spine-possib-phases : ∀{Γ LA U L+ A}
  → Spine Γ (A ∷ LA) L+ U 
  → ((LA ≡ []) × (L+ ≡ []))
         ⊎
  (∃ λ RA → 
     (Spine Γ LA (L+ ++ RA) U) × 
      -- It's important to be able to reconstruct the negative multifocused part
      -- for ANY spine, 
       (∀{LA' L'+ U'} → stable U' → Spine Γ LA' (L'+ ++ RA) U' →  Spine Γ (A ∷ LA') L'+ U'))
spine-possib-phases id⁻ = inj₁ (refl , refl)
spine-possib-phases {Γ} {[]} {U} {L+} {↑ x} (↑L-cons pf N) = 
  inj₂ (x ∷ [] , N , ↑L-cons)
spine-possib-phases {Γ} {x ∷ LA} {A = ↑ x₁} (↑L-cons pf N) with spine-possib-phases N
spine-possib-phases {Γ} {x ∷ LA} {A = ↑ x₁} (↑L-cons pf N) | inj₁ x₂ = inj₂ (x₁ ∷ [] , N , ↑L-cons)
spine-possib-phases {Γ} {x ∷ LA} {A = ↑ x₁} (↑L-cons pf N) | inj₂ y = inj₂ (x₁ ∷ [] , N , ↑L-cons)

spine-possib-phases (⊃L V Sp) with spine-possib-phases Sp
spine-possib-phases (⊃L V Sp) | inj₁ x = inj₁ x
spine-possib-phases (⊃L V Sp) | inj₂ (RA  , Sp' , R)  = 
  inj₂ (RA , Sp' , (λ {x₁} {x₂} {x₃} pf x₄  → ⊃L V (R pf x₄)))

spine-possib-phases (∧⁻L₁ Sp) with spine-possib-phases Sp
spine-possib-phases (∧⁻L₁ Sp) | inj₁ x = inj₁ x
spine-possib-phases (∧⁻L₁ Sp) | inj₂ (RA , Sp' , R) = 
  inj₂ (RA  , Sp' , (λ {x₁} {x₂} {x₃} pf x₄ → ∧⁻L₁ (R pf x₄)))
spine-possib-phases (∧⁻L₂ Sp) with spine-possib-phases Sp
spine-possib-phases (∧⁻L₂ Sp) | inj₁ x = inj₁ x
spine-possib-phases (∧⁻L₂ Sp) | inj₂ (RA , Sp' , R) = 
  inj₂ (RA , Sp' , (λ {x₁} {x₂} {x₃} pf x₄ → ∧⁻L₂ (R pf x₄)))





no-neg-helper1 : ∀{N x L} → N ≡ size-list-formulas (↑ x ∷ L) → N >′ size-list-formulas L
no-neg-helper1 {x = x} refl = suc-+-refl->′ (size-formula x)

no-neg-helper2 : ∀{N x x₁ L} → N ≡ size-list-formulas (x ⊃ x₁  ∷ L) → N >′ size-list-formulas (x₁ ∷ L)
no-neg-helper2 {N} {x} {x₁} {L} Eq  with size-formula-suc {⁺} {x} 
no-neg-helper2 {N} {x} {x₁} {L} Eq | N' , Eq' 
  rewrite Eq | Eq' 
          | sym (assoc-nat 
              {X = N'}
              {Y = size-formula x₁} 
              {Z = foldr (λ x₂ → _+_ (size-formula x₂)) 0 L}) = 
  >′-step (suc-+-refl->′ N') 

-- Check that no negative literal can appear in the decomposition of the
-- negative multifocused list (we don't care if it appears under a ↑)
no-neg-lit-as-residual' : ∀{N} → (L : List (Type ⁻)) → N ≡ size-list-formulas L → Set
no-neg-lit-as-residual'-helper : ∀{N} → (L : List (Type ⁻)) → N >′ size-list-formulas L → Set

no-neg-lit-as-residual'-helper L (>′-refl Eq) = no-neg-lit-as-residual' L Eq 
no-neg-lit-as-residual'-helper L (>′-step Ieq) = no-neg-lit-as-residual'-helper L Ieq

no-neg-lit-as-residual' [] _ = ⊤
no-neg-lit-as-residual' {zero} (x ∷ L) Eq
  with size-formula-suc {⁻} {x}
no-neg-lit-as-residual' {zero} (x ∷ L) Eq | N' , Eq' rewrite Eq' 
  with Eq 
... | () 
no-neg-lit-as-residual' {suc N} (a Q .⁻ ∷ L) x₁ = ⊥
no-neg-lit-as-residual' {suc N} (↑ x ∷ L) Eq =  
  no-neg-lit-as-residual'-helper L (no-neg-helper1 {N = suc N} {x = x} {L = L} Eq) 
no-neg-lit-as-residual' {suc N} (x ⊃ x₁ ∷ L) Eq = 
  no-neg-lit-as-residual'-helper (x₁ ∷ L) (no-neg-helper2 {N = suc N} {x = x} {x₁ = x₁} {L = L} Eq ) 
no-neg-lit-as-residual' {suc N} (⊤⁻ ∷ L) Eq = no-neg-lit-as-residual' {N} L (suc-inj Eq) 
no-neg-lit-as-residual' {suc N} (x ∧⁻ x₁ ∷ L) Eq 
  rewrite sym (assoc-nat
            {X = size-formula x}
            {Y = size-formula x₁}
            {Z = foldr (λ x₂ → _+_ (size-formula x₂)) 0 L}) = 
          no-neg-lit-as-residual' (x ∷ x₁ ∷ L) (suc-inj Eq) 

no-neg-lit-as-residual : (L : List (Type ⁻)) → Set
no-neg-lit-as-residual L = no-neg-lit-as-residual' L refl 




no-neg-lit-helper-std : ∀{L N N' P P'} 
  → no-neg-lit-as-residual'-helper {N} L P
  → no-neg-lit-as-residual' {N'} L P'

no-neg-lit-helper-std {P = >′-refl refl} {refl} NN = NN
no-neg-lit-helper-std {L = L} {N = suc N} {P = >′-step P} NN = no-neg-lit-helper-std {L = L} {P = P} NN


no-neg-lit'-std-std : ∀{L N P N' P'} 
   → no-neg-lit-as-residual' {N} L P
   → no-neg-lit-as-residual' {N'} L P'
no-neg-lit'-std-std {P = refl} {P' = refl} NN = NN 

no-neg-lit-↑ : ∀{x L} → no-neg-lit-as-residual (↑ x ∷ L) →  no-neg-lit-as-residual L
no-neg-lit-↑ {x} {L} NN = 
  no-neg-lit-helper-std 
    {L = L} 
    {N = suc (size-formula x + foldr (λ z → _+_ (size-formula z)) zero L)} 
    {P = suc-+-refl->′ (size-formula x)} NN 

postulate 
  no-neg-lit-⊃ :  ∀{A B L} → no-neg-lit-as-residual (A ⊃ B ∷ L) →  no-neg-lit-as-residual (B ∷ L)

postulate 
  no-neg-lit-∧1 :  ∀{A B L} → no-neg-lit-as-residual (A ∧⁻ B ∷ L) →  no-neg-lit-as-residual (A ∷ L)

postulate 
  no-neg-lit-∧2 :  ∀{A B L} → no-neg-lit-as-residual (A ∧⁻ B ∷ L) →  no-neg-lit-as-residual (B ∷ L)



pos-residuals'' : ∀{Γ Y L2 L+ U}
  → (L1 : List (Type ⁻))
  → (Sp : Spine Γ (L1 ++ (Y ∷ L2)) L+ U)
  → List (Type ⁺)
pos-residuals'' [] Sp = []
-- I have to do this stupid split otherwise Agda cannot pattern match
-- directly on the spine
pos-residuals'' (._ ∷ []) (↑L-cons {X} pf N₁) = [ X ] 
pos-residuals'' (._ ∷ []) (⊃L {A} {B} V Sp) = pos-residuals'' [ B ] Sp 
pos-residuals'' (._ ∷ []) (∧⁻L₁ {A} {B} Sp) = pos-residuals'' [ A ] Sp 
pos-residuals'' (._ ∷ []) (∧⁻L₂ {A} {B} Sp) = pos-residuals'' [ B ] Sp 
--
pos-residuals'' (._ ∷ x₁ ∷ L1) (↑L-cons {X} pf N₁) = X ∷ pos-residuals'' (x₁ ∷ L1) N₁
pos-residuals'' (._ ∷ x₁ ∷ L1) (⊃L {A} {B} V Sp) = pos-residuals'' (B ∷ x₁ ∷ L1) Sp 
pos-residuals'' (._ ∷ x₁ ∷ L1) (∧⁻L₁ {A} {B} Sp) = pos-residuals'' (A ∷ x₁ ∷ L1) Sp
pos-residuals'' (._ ∷ x₁ ∷ L1) (∧⁻L₂ {A} {B} Sp) = pos-residuals'' (B ∷ x₁ ∷ L1) Sp







spine-access-element : ∀{Γ L1 X L2 U L+}
  → (Sp : Spine Γ (L1 ++ X ∷ L2) L+ U)
  → ((L1 ≡ []) × (L2 ≡ []) × (L+ ≡ []))
         ⊎
    (Spine Γ (X ∷ L2) (L+ ++ pos-residuals'' L1 Sp) U) × 
       -- The element X could be generalized to a list...
       (∀{Y} → Spine Γ (Y ∷ L2) (L+ ++ pos-residuals'' L1 Sp) U → Spine Γ (L1 ++ Y ∷ L2) L+ U)
spine-access-element {L1 = []} id⁻ = inj₁ (refl , refl , refl)
spine-access-element {L1 = []} {L+ = L+} (↑L-cons pf N)
  rewrite concat-nil L+ =
    inj₂ (↑L-cons pf N , (λ {Y} z → z))  
spine-access-element {L1 = []} {L+ = L+} (⊃L V Sp)
  rewrite concat-nil L+ = 
    inj₂ (⊃L V Sp , (λ {Y} z → z)) 
spine-access-element {L1 = []} {L+ = L+} (∧⁻L₁ Sp)
  rewrite concat-nil L+ = 
    inj₂ (∧⁻L₁ Sp , (λ {x} x₁ → x₁))
spine-access-element {L1 = []} {L+ = L+} (∧⁻L₂ Sp)
  rewrite concat-nil L+ = 
    inj₂ (∧⁻L₂ Sp , (λ {x} x₁ → x₁))
--
-- I have to do this stupid split otherwise Agda cannot pattern match
-- directly on the spine
spine-access-element {L1 = ._ ∷ []} {X} (↑L-cons pf N) = inj₂ (N , (λ {x} → ↑L-cons pf)) 
spine-access-element {L1 = A ⊃ B ∷ []} (⊃L V Sp)
  with spine-access-element {L1 = B ∷ []} Sp 
... | inj₁ (() , Q) 
... | inj₂ (Sp' , H)  = inj₂ (Sp' , (λ {Y} z → ⊃L V (H z))) 

spine-access-element {L1 = ._ ∷ []} (∧⁻L₁ {A} Sp)
  with spine-access-element {L1 = A ∷ []} Sp 
... | inj₁ (() , x)
... | inj₂ (Sp' , H) = inj₂ (Sp' , (λ {Y} z → ∧⁻L₁ (H z)))  
spine-access-element {L1 = ._ ∷ []} (∧⁻L₂ {A} {B} Sp)
 with spine-access-element {L1 = B ∷ []} Sp 
... | inj₁ (() , x)
... | inj₂ (Sp' , H) = inj₂ (Sp' , (λ {Y} z → ∧⁻L₂ (H z)))   
-----
spine-access-element {L1 = ._ ∷ x ∷ L1} {L+ = L+} (↑L-cons {z} pf N)
  with spine-access-element {L1 = x ∷ L1} N
... | inj₁ (() , _)
... | inj₂ (Sp' , H) rewrite append-nil-cons {X = z} {L1 = L+} {L2 = pos-residuals'' (x ∷ L1) N} 
  = inj₂ (Sp' , (λ {Y} z₁ → ↑L-cons pf (H z₁))) 
spine-access-element {L1 = ._ ∷ x ∷ L1} (⊃L {A} {B} V Sp)
  with spine-access-element {L1 = B ∷ x ∷ L1} Sp 
... | inj₁ (() , _)
... | inj₂ (Sp' , H) = inj₂ (Sp' , (λ {x₁} x₂ → ⊃L V (H x₂))) 
spine-access-element {L1 = ._ ∷ x ∷ L1} (∧⁻L₁ {A} {B} Sp) 
  with spine-access-element {L1 = A ∷ x ∷ L1} Sp
... | inj₁ (() , _)
... | inj₂ (Sp' , H) = inj₂ (Sp' , (λ {Y} z → ∧⁻L₁ (H z)))
spine-access-element {L1 = ._ ∷ x ∷ L1} (∧⁻L₂ {A} {B} Sp) 
  with spine-access-element {L1 = B ∷ x ∷ L1} Sp
... | inj₁ (() , _)
... | inj₂ (Sp' , H) = inj₂ (Sp' , (λ {Y} z → ∧⁻L₂ (H z)))


{-
∧-context-adm : ∀{Γ1 Γ2 A B L} 
  → Exp (Γ1 ++ Pers (A ∧⁻ B) ∷ Γ2)  L
  → suspnormalF L -- needed for the case focL-init 
  → Exp (Γ1 ++ Pers A ∷ Pers B ∷ Γ2)  L


postulate 
  pos-helper : ∀{Γ1 Γ2 A B x L' L- U}
    → (Sp' : Exp (Γ1 ++ Pers (A ∧⁻ B) ∷ Γ2)  (Left (inj₁ (x ∷ L' ++ A ∧⁻ B ∷ L- , [])) U))
    → ∃ λ E → ∃ λ T
      → pos-residuals'' (x ∷ L') Sp' ≡ E ∷ T



TODO
TODO 
TODO: finish 
∧-context-loading-adm : ∀{Γ1 Γ2 A B L- U} 
                        → Spine-l (Γ1 ++ Pers (A ∧⁻ B) ∷ Γ2)  L- U 
                        → suspnormal U 
                        → Spine-l (Γ1 ++ Pers A ∷ Pers B ∷ Γ2)  L- U
-- Even though this lemma is wrong:
--spine-∧-adm : ∀{Γ A B L1 L2 L+ U} → Spine Γ (L1 ++ (A ∧⁻ B) ∷ L2) L+ U → suspnormal U → Spine Γ (L1 ++ A ∷ B ∷ L2) L+ U
-- this one is true.
-- The trick is to go up in the proof to the place where one of the two  ∧⁻ rules
-- is used so we can single focus on the useful component
∧-context-loading-adm {Γ1} (focL-step pf In Sp) pf' with fromctx Γ1 In 
--
-- % We loaded Pers (A ∧⁻ B)
--
∧-context-loading-adm {A = A} {B = B} (focL-step pf In Sp) pf' | inj₁ refl 
   with loading-done-unprecise Sp
--
--    *  This was actually the last step
-- 
∧-context-loading-adm (focL-step pf In Sp) () | inj₁ refl | [] , Sub , id⁻
∧-context-loading-adm {Γ1} {Γ2} {A} {B} (focL-step pf In Sp) pf' | inj₁ refl | [] , Sub , ∧⁻L₁ Sp₁ = 
  focL-step {A = A} 
    pf 
    (in-append-right {L1 = Γ1} (here refl)) 
    (focL-end pf (∧-context-adm {Γ1} {Γ2} {A} {B} Sp₁ pf'))
∧-context-loading-adm {Γ1} {Γ2} {A} {B} (focL-step pf In Sp) pf' | inj₁ refl | [] , Sub , ∧⁻L₂ Sp₁ = 
  focL-step {A = B} 
    pf 
    (in-append-right {L1 = Γ1} (there (here refl))) 
    (focL-end pf (∧-context-adm {Γ1} {Γ2} {A} {B} Sp₁ pf'))
--
--    *  It was not the last step
-- 
∧-context-loading-adm {Γ1} {Γ2} {A} {B} {L- } {U} (focL-step pf In Sp) pf' | inj₁ refl | x ∷ L' , Sub , Sp' 
        -- The loading phase is done.        -- However the conjunction is in the middle of list
        -- We thus have to take care of the first elements preceding the conjunction
  with spine-access-element {L1 = x ∷ L'} Sp' 
... | inj₁ (() , _ , _) 
... | inj₂ (Sp'' , H) with pos-helper {Γ1} {Γ2} {A} {B} {x} {L'} {L- } Sp'
          -- We need to rule out the id- case so we rewrite
          -- an can finally pattern match on Sp''
... | E , T , Eq rewrite Eq with Sp''
... | ∧⁻L₁ Sp1 = focL-step {A = A} 
                           pf 
                           (in-append-right {L1 = Γ1} (here refl) ) 
                           (unload-partial-l 
                               (x ∷ L') 
                               pf 
                               (focL-end pf (∧-context-adm {Γ1} {Γ2} {A} {B} (H {A} Sp1) pf')) 
                               {!!}) 
... | ∧⁻L₂ Sp2 = {!!} 
--
-- % We loaded something else than Pers (A ∧ B)
--  
∧-context-loading-adm (focL-step pf In Sp) pf' | inj₂ y = {!!} 
∧-context-loading-adm (focL-end pf Sp) pf' = {!!} 





∧-context-adm {Γ1} (id⁺ v) pf with fromctx Γ1 v 
∧-context-adm (id⁺ v) pf | inj₁ ()
... | inj₂ X = id⁺ (in-append-double-weak {L1 = Γ1} X)
∧-context-adm {Γ1} (↓R N) pf = ↓R (∧-context-adm {Γ1} N pf)
∧-context-adm {Γ1} (∨R₁ V) pf = ∨R₁ (∧-context-adm {Γ1} V pf)
∧-context-adm {Γ1} (∨R₂ V) pf = ∨R₂ (∧-context-adm {Γ1} V pf)
∧-context-adm {Γ1} ⊤⁺R _ = ⊤⁺R
∧-context-adm {Γ1} (∧⁺R V₁ V₂) pf = ∧⁺R (∧-context-adm {Γ1}  V₁ pf) (∧-context-adm {Γ1}  V₂ pf)
∧-context-adm {Γ1} (focR V) pf = focR (∧-context-adm {Γ1}  V pf)
∧-context-adm {Γ1} {Γ2} {A = A} {B = B} (focL-init pf Sp) pf'
  = load-std {Γ = Γ1 ++ Pers A ∷ Pers B ∷ Γ2} (∧-context-loading-adm {Γ1} {Γ2} {A = A} {B = B} Sp pf')
∧-context-adm {Γ1} (η⁺ {Q} N) pf = η⁺ (∧-context-adm {Γ1 = HSusp (a Q ⁺) ∷ Γ1}  N pf)
∧-context-adm {Γ1} (↓L {A₁} N) pf = ↓L (∧-context-adm {Γ1 = Pers A₁ ∷ Γ1}  N pf)
∧-context-adm {Γ1} ⊥L _ = ⊥L
∧-context-adm {Γ1} (∨L N₁ N₂) pf = ∨L (∧-context-adm {Γ1} N₁ pf) (∧-context-adm {Γ1} N₂ pf)
∧-context-adm {Γ1} (⊤⁺L N) pf = ⊤⁺L (∧-context-adm {Γ1} N pf)
∧-context-adm {Γ1} (∧⁺L N) pf = ∧⁺L (∧-context-adm {Γ1} N pf)
∧-context-adm {Γ1} (η⁻ N) pf = η⁻ (∧-context-adm {Γ1} N pf)
∧-context-adm {Γ1} (↑R N) pf = ↑R (∧-context-adm {Γ1} N pf)
∧-context-adm {Γ1} (⊃R N) pf = ⊃R (∧-context-adm {Γ1} N pf)
∧-context-adm {Γ1} ⊤⁻R pf = ⊤⁻R
∧-context-adm {Γ1} (∧⁻R N₁ N₂) pf = ∧⁻R (∧-context-adm {Γ1}  N₁ pf) (∧-context-adm {Γ1}  N₂ pf)
∧-context-adm {Γ1} id⁻ pf = id⁻
∧-context-adm {Γ1} (↑L-cons pf N) pf' = ↑L-cons pf (∧-context-adm {Γ1}  N pf')
∧-context-adm {Γ1} (↑L-nil pf N) pf' = ↑L-nil pf (∧-context-adm {Γ1}  N pf')
∧-context-adm {Γ1} (⊃L V Sp) pf = ⊃L (∧-context-adm {Γ1} V tt) (∧-context-adm {Γ1}  Sp pf)
∧-context-adm {Γ1} (∧⁻L₁ Sp) pf = ∧⁻L₁ (∧-context-adm {Γ1}  Sp pf)
∧-context-adm {Γ1} (∧⁻L₂ Sp) pf = ∧⁻L₂ (∧-context-adm {Γ1}  Sp pf)


-}






unload-all-term : ∀{Γ U} 
  → (L : List (Type ⁻)) 
  → (pf : stable U) 
  → Spine Γ L [] U 
  → Data.List.map Pers L ⊆ Γ 
  → Term Γ [] U 
unload-all-term L- pf Sp In = focL-init pf (unload-all-l L-  pf (focL-end pf Sp) In) 


{-
unload-one-adm : ∀{Γ X Y L- L+ U} 
  → (pf : stable U) 
  → Spine Γ (Y ∷ L-) (X ∷ L+) U 
  → Data.List.map Pers (Y ∷ L-) ⊆ Γ 
  → Spine Γ L- (X ∷ L+) U 
unload-one-adm {Y = a Q .⁻} pf () Sub
unload-one-adm {Y = ↑ x} {[]} pf (↑L-cons pf₁ N) Sub = {!!}
unload-one-adm {Y = ↑ x} {x₁ ∷ L- } pf (↑L-cons pf₁ N) Sub = {!!}
unload-one-adm {Y = A ⊃ B} pf (⊃L V Sp) Sub = {!!}
unload-one-adm {Y = ⊤⁻} pf () Sub
unload-one-adm {Y = A ∧⁻ Y₁} pf (∧⁻L₁ Sp) Sub = {!!}
unload-one-adm {Y = A ∧⁻ Y₁} pf (∧⁻L₂ Sp) Sub = {!!}
-}


postulate
  in-sub-eq : ∀{A B L Γ} → Pers (A ∧⁻ B) ∷ L ⊆ Γ 
    →  ∃ λ Γ1 → ∃ λ Γ2 → Γ ≡ Γ1 ++ Pers (A ∧⁻ B) ∷ Γ2

{-
TODO TODO TODO
unload-all-adm-bis : ∀{Γ X L- L+ U} 
  → (pf : stable U) 
  → Spine Γ L- (X ∷ L+) U 
  → Data.List.map Pers L- ⊆ Γ 
  → Spine Γ [] (X ∷ L+) U 
unload-all-adm-bis {L+ = []} pf (↑L-cons {y} pf₁ N) Sub = 
  cntr-+-[]-spine pf (y) (unload-all-adm-bis pf₁ N (λ {x} z → Sub (there z)) ) (Sub (here refl)) 
unload-all-adm-bis {L+ = []} pf (↑L-nil pf₁ N) Sub = ↑L-nil pf₁ N
unload-all-adm-bis {L+ = []} pf (⊃L V Sp) Sub = {!!}
unload-all-adm-bis {L+ = []} pf (∧⁻L₁ Sp) Sub 
  with in-sub-eq Sub
... | Γ1 , Γ2 , Eq rewrite Eq = {!∧-context-adm !} 
unload-all-adm-bis {L+ = []} pf (∧⁻L₂ Sp) Sub = {!!}
unload-all-adm-bis {L+ = x ∷ L+} pf Sp Sub = {!!}
-}


unload-partial-adm-bis : ∀{Γ X L1 L2 L+ U} 
  → (pf : stable U) 
  → Spine Γ (L1 ++ L2)  (X ∷ L+) U 
  → Data.List.map Pers L1 ⊆ Γ 
  → Spine Γ L2 (X ∷ L+) U 
unload-partial-adm-bis {L1 = []} pf Sp Sub = Sp
unload-partial-adm-bis {L1 = ._ ∷ L1} pf (↑L-cons {Y} pf₁ N) Sub = 
  -- Requires cntr-+-L-spine and thus suspnormal U as a condition
  {!↑L-cons ? (unload-partial-adm-bis pf₁ N ?)!}
unload-partial-adm-bis {L1 = ._ ∷ L1} pf (⊃L V Sp) Sub = {!!}
unload-partial-adm-bis {L1 = ._ ∷ L1} pf (∧⁻L₁ Sp) Sub = {!!}
unload-partial-adm-bis {L1 = ._ ∷ L1} pf (∧⁻L₂ Sp) Sub = {!!}




{-
unload-all-adm : ∀{Γ X L- L+ U} 
  → (pf : stable U) 
  → Spine Γ L- (X ∷ L+) U 
  → Data.List.map Pers L- ⊆ Γ 
  → Spine Γ [] (X ∷ L+) U 
unload-all-adm {L- = []} pf Sp Sub = Sp
unload-all-adm {L- = x ∷ L- } pf Sp Sub = unload-all-adm pf (unload-one-adm pf Sp Sub) (λ {x₁} z → Sub (there z))
-}




spine-init : ∀{Γ Q LA U L+}
  → Spine Γ (a Q ⁻ ∷ LA) L+ U 
  → ((LA ≡ []) × (L+ ≡ []))
spine-init id⁻ = refl , refl








{-has-atomic-residual : Type ⁻ → Bool
has-atomic-residual (a Q .⁻) = true
has-atomic-residual (↑ x) = {!!}
has-atomic-residual (x ⊃ x₁) = {!!}
has-atomic-residual ⊤⁻ = false
has-atomic-residual (x ∧⁻ x₁) = {!!} --has-atomic-residual x  || has-atomic-residual x₁
-}


{-
--TODO: Generalize with suspended formula and residuals, otherwise this is not true
spine-⊥ : ∀{Γ L- L+ U} → stable U →  (Spine Γ L- (⊥⁺ ∷ L+) U ⊎ ∃ λ Q → (a Q ⁻ ∈ L-))
spine-⊥ {L- = []} pf = inj₁ (↑L-nil pf ⊥L)
spine-⊥ {L- = a Q .⁻ ∷ L- } pf = inj₂ (Q , here refl)
spine-⊥ {L- = ↑ x ∷ L- } pf = {!!}
spine-⊥ {L- = x ⊃ x₁ ∷ L- } pf = {!!}
spine-⊥ {L- = ⊤⁻ ∷ L- } pf = {!!}
spine-⊥ {Γ} {x ∧⁻ x₁ ∷ L- } {L+} {U} pf with spine-⊥ {Γ} {L- } {L+} {U} pf  
spine-⊥ {Γ} {x₁ ∧⁻ x₂ ∷ L- } pf | inj₁ x = {!!} --TODO: Weaken
spine-⊥ {Γ} {x ∧⁻ x₁ ∷ L- } pf | inj₂ (Q , In) =  inj₂ (Q , there In)

spine'-⊥ : ∀{Γ L- L+ U} → stable U →  All (λ x → ∀{Q} → x ≢ a Q ⁻) L- → Spine Γ L- (⊥⁺ ∷ L+) U 
spine'-⊥ {L- = []} pf All = ↑L-nil pf ⊥L
spine'-⊥ {L- = a Q .⁻ ∷ xs} pf (px ∷ All) = ⊥-elim (px refl)
spine'-⊥ {L- = ↑ x ∷ L- } pf All = {!!}
spine'-⊥ {L- = x ⊃ x₁ ∷ L- } pf All = {!!}
spine'-⊥ {L- = ⊤⁻ ∷ L- } pf All = {!!}
spine'-⊥ {L- = x ∧⁻ x₁ ∷ L- } pf (px ∷ All) = {!spine'-⊥ pf All!}
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



