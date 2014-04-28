open import Data.List
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open import Data.Empty
open import Data.List 
open import Data.List.All
open import Data.Nat  hiding (_≤′_; module _≤′_; _<′_; _≥′_; _>′_)
open import Data.Sum 
open import Data.Product

open import Foc
open import FocProps
open import NatExtra
open import Weak
open import ListExtra

module FocSubst where


subst⁺-help : ∀{Γ A Form z} 
  → (Γ' : Ctx)
  → Value (Γ' ++ Γ) A
  → (e : Exp (Γ' ++ HSusp A ∷ Γ) Form)
  → (z >′ height e)
  → Exp (Γ' ++ Γ) Form

subst⁺ : ∀{Γ A Form z} 
  → (Γ' : Ctx)
  → Value (Γ' ++ Γ) A
  → (e : Exp (Γ' ++ HSusp A ∷ Γ) Form)
  → (z ≡ height e)
  → Exp (Γ' ++ Γ) Form

subst⁺-help Γ' V E (>′-refl m≡n) = subst⁺ Γ' V E m≡n
subst⁺-help Γ' V E (>′-step H) = subst⁺-help Γ' V E H



subst⁺ {z = zero} Γ' V E H =  ⊥-elim (zero-height-absurd (sym H))
subst⁺ {z = suc z'} Γ' V (id⁺ x) _ with fromctx Γ' x
subst⁺ {z = suc z'} Γ' V (id⁺ x) _ | inj₁ refl = V
subst⁺ {z = suc z'} Γ' V (id⁺ x) _ | inj₂ y = id⁺ y
subst⁺ {z = suc z'} Γ' V (↓R N) H = ↓R (subst⁺ Γ' V N (suc-inj H))
subst⁺ {z = suc z'} Γ' V (∨R₁ V') H = ∨R₁ (subst⁺ Γ' V V' (suc-inj H))
subst⁺ {z = suc z'} Γ' V (∨R₂ V') H = ∨R₂ (subst⁺ Γ' V V' (suc-inj H))
subst⁺ {z = suc z'} Γ' V ⊤⁺R _ = ⊤⁺R
subst⁺ {z = suc z'} Γ' V (∧⁺R V₁ V₂) H = 
   ∧⁺R 
     (subst⁺-help Γ' V V₁ (suc-max-left H)) 
     (subst⁺-help Γ' V V₂ (suc-max-right {x = height V₁}  H))
subst⁺ {z = suc z'} Γ' V (focR V') H = focR (subst⁺ Γ' V V' (suc-inj H))

subst⁺ {Γ} {A} {z = suc z'} Γ' V (focL-init pf Sp) H with loading-done Sp
... | L'  , Sub , Exp , Ieq rewrite concat-nil L' = 
  unload-all 
    L' 
    pf 
    ((subst⁺-help Γ' V Exp ( (subst (\x → x  >′ height Exp) (sym H) (>′-step Ieq))))) 
    ((pers-hsusp-subset {Γ = Γ} {Γ' = Γ'} Sub))
    
subst⁺ {z = suc z'} Γ' V (η⁺ N) H = η⁺ (subst⁺ (_ ∷ Γ') (wken V) N (suc-inj H))
subst⁺ {z = suc z'} Γ' V (η⁻ N) H = η⁻ (subst⁺ Γ' V N (suc-inj H))
subst⁺ {z = suc z'} Γ' V (↓L N) H = ↓L (subst⁺ (_ ∷ Γ') (wken V) N (suc-inj H))
subst⁺ {z = suc z'} Γ' V (↑R N) H = ↑R (subst⁺ Γ' V N (suc-inj H))
subst⁺ {z = suc z'} Γ' V ⊥L _ = ⊥L
subst⁺ {z = suc z'} Γ' V (∨L N₁ N₂) H = 
  ∨L (subst⁺-help Γ' V N₁ (suc-max-left H)) (subst⁺-help Γ' V N₂ (suc-max-right {x = height N₁} H))
subst⁺ {z = suc z'} Γ' V (⊤⁺L N) H = ⊤⁺L (subst⁺ Γ' V N (suc-inj H))
subst⁺ {z = suc z'} Γ' V (∧⁺L N) H = ∧⁺L (subst⁺ Γ' V N (suc-inj H))
subst⁺ {z = suc z'} Γ' V (⊃R N) H = ⊃R (subst⁺ Γ' V N (suc-inj H))
subst⁺ {z = suc z'} Γ' V ⊤⁻R _ = ⊤⁻R
subst⁺ {z = suc z'} Γ' V (∧⁻R N₁ N₂) H = 
  ∧⁻R (subst⁺-help Γ' V N₁ (suc-max-left H)) (subst⁺-help Γ' V N₂ (suc-max-right {x = height N₁} H))
subst⁺ {z = suc z'} Γ' V id⁻ _ = id⁻
subst⁺ {z = suc z'} Γ' V (↑L-nil pf N) H = ↑L-nil pf (subst⁺ Γ' V N (suc-inj H))
subst⁺ {z = suc z'} Γ' V (↑L-cons pf N) H = ↑L-cons pf (subst⁺ Γ' V N (suc-inj H)) 
subst⁺ {z = suc z'} Γ' V (⊃L V' Sp) H = 
  ⊃L (subst⁺-help Γ' V V' (suc-max-left H)) (subst⁺-help Γ' V Sp (suc-max-right {x = height V'} H))
subst⁺ {z = suc z'} Γ' V (∧⁻L₁ Sp) H = ∧⁻L₁ (subst⁺ Γ' V Sp (suc-inj H))
subst⁺ {z = suc z'} Γ' V (∧⁻L₂ Sp) H = ∧⁻L₂ (subst⁺ Γ' V Sp (suc-inj H))


  

subst⁻-help : ∀{Γ A L U z}
  → stable U
  → (e : Exp Γ (Left L (Susp A)))
  → (z >′ height e)
  → Spine Γ [ A ] [] U
  → Exp Γ (Left L U)

subst⁻ : ∀{Γ A L U z}
  → stable U
  → (e : Exp Γ (Left L (Susp A)))
  → (z ≡ height e)
  → Spine Γ [ A ] [] U
  → Exp Γ (Left L U)

subst⁻-help pf Exp (>′-refl m≡n) Sp = subst⁻ pf Exp m≡n Sp
subst⁻-help pf Exp (>′-step Ineq) Sp = subst⁻-help pf Exp Ineq Sp


subst⁻  {z = zero} pf _ H Sp' = ⊥-elim (zero-height-absurd (sym H))
subst⁻  {Γ} {A} {z = z} pf (focL-init pf' Sp) H Sp' with loading-done Sp
... | L'  , Sub , Exp , Ieq rewrite concat-nil L'  = unload-all 
    L' 
    pf 
    (subst⁻-help {z = z} 
                 pf 
                 Exp 
                 (subst (\x → x  >′ height Exp) (sym H) (>′-step Ieq))
                 Sp'
    ) 
    Sub  
subst⁻ {z = suc z'} pf (↓L N) H Sp = ↓L (subst⁻ pf N ((suc-inj H)) (wken Sp))
subst⁻ {z = suc z'} pf (η⁺ N) H Sp = η⁺ (subst⁻ pf N (suc-inj H) (wken Sp))
subst⁻  {z = suc z'} pf ⊥L H Sp = ⊥L
subst⁻  {z = suc z'} pf (∨L N₁ N₂) H Sp = 
  ∨L 
    (subst⁻-help {z = suc z'} pf N₁ (suc-max-left H) Sp) 
    (subst⁻-help {z = suc z'} pf N₂ (suc-max-right {x = height N₁} H) Sp)  
subst⁻  {z = suc z'} pf (⊤⁺L N) H Sp = ⊤⁺L (subst⁻ pf N (suc-inj H) Sp)
subst⁻  {z = suc z'} pf (∧⁺L N) H Sp = ∧⁺L (subst⁻ pf N (suc-inj H) Sp)
subst⁻  {z = suc z'} pf id⁻ H Sp = Sp
subst⁻  {z = suc z'} pf (↑L-cons pf₁ N) H Sp = ↑L-cons pf (subst⁻ pf N (suc-inj H) Sp) 
subst⁻ {z = suc z'} pf (↑L-nil pf₁ N) H Sp = ↑L-nil pf (subst⁻ pf N (suc-inj H) Sp)
subst⁻  {z = suc z'} pf (⊃L V Sp) H Sp' = 
  ⊃L V (subst⁻-help pf Sp (suc-max-right {x = height V} H) Sp')
subst⁻ {z = suc z'} pf (∧⁻L₁ Sp) H Sp' =  ∧⁻L₁ (subst⁻ pf Sp (suc-inj H) Sp') 
subst⁻ {z = suc z'} pf (∧⁻L₂ Sp) H Sp' = ∧⁻L₂ (subst⁻ pf Sp (suc-inj H) Sp') 




{- Not true, with the case L+ = [] 
subst-term : ∀{Γ L+ U}
  → stable U
  → (LA : List (Type ⁻))
  → All (\x → Term Γ L+ (Susp x)) LA
  → Spine Γ LA [] U
  → Spine Γ [] L+ U

Not true, with the case LA = []

gsubst-term- : ∀{Γ L+ A LA U}
  → stable U
  → Term Γ L+ (Susp A)
  → Spine Γ (A ∷ LA) [] U
  → Spine Γ LA [] U
-}


{-
This seems to be not true with the following case:

Γ ; [A , Ω | Δ] ⊢ A1 
----------------------
Γ ; [A ∧ B, Ω | Δ] ⊢ A1   ...  Γ ; [A ∧ B, Ω | Δ] ⊢ An    Γ ; [A1 ... An| ] ⊢ U
-------------------------------------------------------------------------------

We cannot apply induction hypothesis since we cannot guarantee that 
was the ∧ left rule which was applied on all the premises.

gsubst-term-x : ∀{Γ L U}
  → stable U
  → (LA : List (Type ⁻))
  → All (\x → Exp Γ (Left L (Susp x))) LA
  → Spine Γ LA [] U
  → Exp Γ (Left L U)

If we want to generalize with something like:
→ All (\x → \y → Exp Γ (Left y (Susp x))) LA LL
then we can have spine and terms appearing as premises
and the result is far from obvious...
-}

fuse : List ((List (Type ⁻) × List (Type ⁺)) ⊎ List (Type ⁺))
  → List (Type ⁻) × List (Type ⁺) 
fuse [] = ([] , [])
fuse (inj₁ (L- , L+) ∷ L) = L- ++ proj₁ (fuse L) , L+ ++ proj₂ (fuse L)
fuse (inj₂ L+ ∷ L)  = proj₁ (fuse L) , L+ ++ proj₂ (fuse L)



{- This cannot work either due to the following case (amongst others):
-Γ ; A+  , B+  Ω1  ⊢ <A1> 
---------------------
-Γ ; A+ ∧⁺ B+ , Ω1 ⊢ <A1>  ...  Γ ; L ⊢ <An>    Γ ; [A1 ... An] ⊢ U
---------------------------------------------------------------
 
-If we apply the i.h. then we get 
 
-Γ ; [Δ2 ... Δn | A+ , B+ , Ω1 , Ξ2 ... Ξn ] ⊢ U
 
-and we are stuck. At least I don't know how to do. -}


{- Maybe .... -}



gsubst-gen : ∀{Γ LL U}
  → stable U
  → (LA : List (Type ⁻))
  → All (\x →  Exp Γ (Left (proj₁ x) (Susp (proj₂ x)))) (Data.List.zip LL  LA)
  → length LL ≡ length LA
  → Spine Γ LA [] U
  → Exp Γ (Left (inj₁ (fuse LL)) U)
gsubst-gen {LL = []} pf [] Exps Eq Sp = Sp
gsubst-gen {LL = x ∷ LL} pf [] Exps () Sp
gsubst-gen {LL = []} pf (x ∷ LA) Exps () Sp
gsubst-gen {LL = .(inj₂ []) ∷ LL} pf (x₁ ∷ LA) (focL-init pf₁ Sp ∷ Exps) Eq Sp₁ = {!!}
gsubst-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (η⁺ N ∷ Exps) Eq Sp = {!!}
gsubst-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (↓L N ∷ Exps) Eq Sp = {!!}
gsubst-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (⊥L ∷ Exps) Eq Sp = {!!}
gsubst-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (∨L N₁ N₂ ∷ Exps) Eq Sp = 
  spine-∨-adm (gsubst-gen pf (x₁ ∷ LA) (N₁ ∷ Exps) Eq Sp) (gsubst-gen pf (x₁ ∷ LA) (N₂ ∷ Exps) Eq Sp ) 
gsubst-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (⊤⁺L N ∷ Exps) Eq Sp = 
 spine-⊤⁺-adm  (gsubst-gen pf (x₁ ∷ LA) (N ∷ Exps) Eq Sp)
gsubst-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (∧⁺L N ∷ Exps) Eq Sp = 
  spine-∧⁺-adm (gsubst-gen pf (x₁ ∷ LA) (N ∷ Exps) Eq Sp)

gsubst-gen {LL = .(inj₁ (x₁ ∷ [] , [])) ∷ LL} pf (x₁ ∷ LA) (id⁻ ∷ Exps) Eq Sp = 
  {!!}
-- The only way to be able to apply the induction hypothesis is to
-- generalize the spine with a possibly non-empty list of positives
-- Thus we can pattern match on the first negative element and apply i.h.
gsubst-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (↑L-cons {L+ = L+} pf₁ N ∷ Exps) Eq Sp = 
  spine-↑-adm 
    {L1 = L+} 
    {L2 = proj₂ (fuse LL)} 
      (gsubst-gen pf (x₁ ∷ LA) (N ∷ Exps) Eq Sp)
gsubst-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (↑L-nil pf₁ N ∷ Exps) Eq Sp = gsubst-gen pf (x₁ ∷ LA) (N ∷ Exps) Eq Sp
gsubst-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (⊃L V Sp ∷ Exps) Eq Sp₁ = ⊃L V (gsubst-gen pf (x₁ ∷ LA) (Sp ∷ Exps) Eq Sp₁)
gsubst-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (∧⁻L₁ Sp ∷ Exps) Eq Sp₁ = ∧⁻L₁  (gsubst-gen pf (x₁ ∷ LA) (Sp ∷ Exps) Eq Sp₁) 
gsubst-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (∧⁻L₂ {L- = L-} {L+ = L+} Sp ∷ Exps) Eq Sp₁ = 
 ∧⁻L₂  (gsubst-gen pf (x₁ ∷ LA) (Sp ∷ Exps) Eq Sp₁) 



fuse-gen : List ((List (Type ⁻) × List (Type ⁺)) ⊎ List (Type ⁺))
  → List (Type ⁺) → List (Type ⁻) × List (Type ⁺) 
fuse-gen [] LL+ = ([] , LL+)
fuse-gen (inj₁ (L- , L+) ∷ L) LL+ = L- ++ proj₁ (fuse-gen L LL+) , L+ ++ proj₂ (fuse-gen L LL+)
fuse-gen (inj₂ L+ ∷ L) LL+ = proj₁ (fuse-gen L LL+) , L+ ++ proj₂ (fuse-gen L LL+)




gsubst-more-gen : ∀{Γ LL L+ U}
  → stable U
  → (LA : List (Type ⁻))
  → All (\x →  Exp Γ (Left (proj₁ x) (Susp (proj₂ x)))) (Data.List.zip LL  LA)
  → length LL ≡ length LA
  → Spine Γ LA L+ U
  → Exp Γ (Left (inj₁ (fuse-gen LL L+)) U)
gsubst-more-gen {LL = []} pf [] Exps Eq Sp = Sp
gsubst-more-gen {LL = x ∷ LL} pf [] Exps () Sp
gsubst-more-gen {LL = []} pf (x ∷ LA) Exps () Sp
gsubst-more-gen {LL = .(inj₂ []) ∷ LL} pf (x₁ ∷ LA) (focL-init pf₁ Sp ∷ Exps) Eq Sp₁ = {!!}
gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (η⁺ N ∷ Exps) Eq Sp = {!!}
gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (↓L N ∷ Exps) Eq Sp = {!!}
gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (⊥L ∷ Exps) Eq Sp = {!!}
gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (∨L N₁ N₂ ∷ Exps) Eq Sp = 
  spine-∨-adm (gsubst-more-gen pf (x₁ ∷ LA) (N₁ ∷ Exps) Eq Sp) (gsubst-more-gen pf (x₁ ∷ LA) (N₂ ∷ Exps) Eq Sp ) 
gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (⊤⁺L N ∷ Exps) Eq Sp = 
 spine-⊤⁺-adm  (gsubst-more-gen pf (x₁ ∷ LA) (N ∷ Exps) Eq Sp)
gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (∧⁺L N ∷ Exps) Eq Sp = 
  spine-∧⁺-adm (gsubst-more-gen pf (x₁ ∷ LA) (N ∷ Exps) Eq Sp)

------------------
gsubst-more-gen {LL = .(inj₁ (a Q ⁻ ∷ [] , [])) ∷ LL} pf (a Q .⁻ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ 
  with length-cons-nil {L = LL} Eq  
gsubst-more-gen {Γ} {.(inj₁ ([ a Q ⁻ ] , [])) ∷ .[]} pf (a Q .⁻ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ | refl = 
  id⁻

gsubst-more-gen {LL = .(inj₁ (↑ x₁ ∷ [] , [])) ∷ LL} pf (↑ x₁ ∷ LA) (id⁻ ∷ Exps) Eq Sp  = {!!}
gsubst-more-gen {LL = .(inj₁ (x₁ ⊃ x₂ ∷ [] , [])) ∷ LL} pf (x₁ ⊃ x₂ ∷ LA) (id⁻ ∷ Exps) Eq Sp = {!!}

gsubst-more-gen {LL = .(inj₁ (⊤⁻ ∷ [] , [])) ∷ LL} pf (⊤⁻ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ 
  with length-cons-nil {X = inj₁ ([ ⊤⁻ ] , [])} {Y = ⊤⁻} {L = LL} Eq 
gsubst-more-gen {Γ} {.(inj₁ ([ ⊤⁻ ] , [])) ∷ .[]} pf (⊤⁻ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ | refl = id⁻

gsubst-more-gen {LL = .(inj₁ (x₁ ∧⁻ x₂ ∷ [] , [])) ∷ LL} pf (x₁ ∧⁻ x₂ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ 
  with length-cons-nil {X = inj₁ (([ x₁ ∧⁻ x₂ ] , []))} {Y = x₁ ∧⁻ x₂ } {L = LL} Eq 
gsubst-more-gen {Γ} {.(inj₁ ([ x₁ ∧⁻ x₂ ] , [])) ∷ .[]} pf (x₁ ∧⁻ x₂ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ | refl = id⁻

gsubst-more-gen {LL = .(inj₁ (x₁ ∧⁻ x₂ ∷ [] , [])) ∷ LL} pf (x₁ ∧⁻ x₂ ∷ LA) (id⁻ ∷ Exps) Eq (∧⁻L₁ Sp) = {!!}
gsubst-more-gen {LL = .(inj₁ (x₁ ∧⁻ x₂ ∷ [] , [])) ∷ LL} pf (x₁ ∧⁻ x₂ ∷ LA) (id⁻ ∷ Exps) Eq (∧⁻L₂ Sp) = {!!}
------------------


gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (↑L-cons {L+ = L+} pf₁ N ∷ Exps) Eq Sp = 
  spine-↑-adm 
    {L1 = L+} 
    (gsubst-more-gen pf (x₁ ∷ LA) (N ∷ Exps) Eq Sp) 
gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (↑L-nil pf₁ N ∷ Exps) Eq Sp = gsubst-more-gen pf (x₁ ∷ LA) (N ∷ Exps) Eq Sp
gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (⊃L V Sp ∷ Exps) Eq Sp₁ = ⊃L V (gsubst-more-gen pf (x₁ ∷ LA) (Sp ∷ Exps) Eq Sp₁)
gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (∧⁻L₁ Sp ∷ Exps) Eq Sp₁ = ∧⁻L₁  (gsubst-more-gen pf (x₁ ∷ LA) (Sp ∷ Exps) Eq Sp₁) 
gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (∧⁻L₂ {L- = L-} {L+ = L+} Sp ∷ Exps) Eq Sp₁ = 
 ∧⁻L₂  (gsubst-more-gen pf (x₁ ∷ LA) (Sp ∷ Exps) Eq Sp₁) 











 
{- This particular case where premisses are only terms.
  -}

gsubst-term : ∀{Γ L+ U}
  → stable U
  → (LA : List (Type ⁻))
  → All (\x → Term Γ L+ (Susp x)) LA
  → Spine Γ LA [] U
  → Term Γ L+ U

gsubst-term pf [] Ts Sp =  ⊥-elim (spine-[]-[] Sp)
gsubst-term pf (x ∷ xs) (focL-init pf₁ Sp ∷ Ts) Sp₁ with loading-done Sp
... | L'  , Sub , Exp , Ieq rewrite concat-nil L'  = 
  {- The problem here is that this is not always the case that there exists a Term above in the derivation 
  
 ----------------
  Γ ; [A1-|] ⊢ <A1->
  --------------
  --------------
  Γ ; . ⊢ <A1->   ....  Γ  ; . ⊢ <An>    Γ ; [A1- ... An-| ] ⊢ U
    --------------------------------------------------------------

How can we conclude that 
Γ ; A1 ... An ⊢ U     (knowing that A1 ∈ Γ)

In the single focused case we would have: 
  ---------------
  Γ; [A-|] ⊢ <A->
  --------------
  --------------
  Γ ; . ⊢ <A>     Γ ; [A ] ⊢ U
  ------------------------------
  
 and we have to show that 
 Γ ; . ⊢ U

By i.h. Γ ; [A-|] ⊢ U 
As A- ∈ Γ we can unload it and obtain the result.

-}
  unload-all 
    L' 
    pf 
    {!!} 
    Sub
gsubst-term pf (x ∷ xs) (η⁺ N ∷ Ts) Sp = η⁺ (gsubst-term pf (x ∷ xs) (N ∷ η+-inv-all xs Ts) (wken Sp))
gsubst-term pf (x ∷ xs) (↓L N ∷ Ts) Sp = ↓L (gsubst-term pf (x ∷ xs) (N ∷ ↓-inv-all xs Ts) (wken Sp))
gsubst-term pf (x ∷ xs) (⊥L ∷ Ts) Sp = ⊥L
gsubst-term pf (x ∷ xs) (∨L N₁ N₂ ∷ Ts) Sp = 
  ∨L 
    (gsubst-term pf (x ∷ xs) (N₁ ∷ ∨+l-inv-all xs Ts ) Sp) 
    (gsubst-term pf (x ∷ xs) (N₂ ∷ ∨+r-inv-all xs Ts ) Sp) 
gsubst-term pf (x ∷ xs) (⊤⁺L N ∷ Ts) Sp = ⊤⁺L (gsubst-term pf (x ∷ xs) (N ∷ ⊤+-inv-all xs Ts) Sp)
gsubst-term pf (x ∷ xs) (∧⁺L N ∷ Ts) Sp = ∧⁺L (gsubst-term pf (x ∷ xs) (N ∷ ∧+-inv-all xs Ts) Sp)



{- True ? Useful ?
gsubst⁻ : ∀{Γ A L- L+ L+' U}
  → stable U
  → Spine Γ L- L+ (Susp A)
  → Spine Γ  [ A ]  L+' U
  → Spine Γ L- (L+ ++ L+') U


gsubst⁻ pf (focL-init pf₁ Sp) Sp₁ with loading-done Sp
... | L'  , Sub , Exp , Ieq rewrite concat-nil L'  = {!gsubst⁻ pf Exp Sp₁!}
gsubst⁻ pf (η⁺ N) Sp = {!!}
gsubst⁻ pf (↓L N) Sp = {!!}
gsubst⁻ pf ⊥L Sp = ⊥L
gsubst⁻ pf (∨L N₁ N₂) Sp = ∨L (gsubst⁻ pf N₁ Sp) (gsubst⁻ pf N₂ Sp)
gsubst⁻ pf (⊤⁺L N) Sp = ⊤⁺L (gsubst⁻ pf N Sp)
gsubst⁻ pf (∧⁺L N) Sp = ∧⁺L (gsubst⁻ pf N Sp)
gsubst⁻ pf id⁻ Sp = Sp
gsubst⁻ pf (↑L-cons pf₁ N) Sp = ↑L-cons pf (gsubst⁻ pf N Sp)
gsubst⁻ pf (↑L-nil pf₁ N) Sp = gsubst⁻ pf N Sp
gsubst⁻ pf (⊃L V Sp) Sp₁ = ⊃L V (gsubst⁻ pf Sp Sp₁)
gsubst⁻ pf (∧⁻L₁ Sp) Sp₁ = ∧⁻L₁ (gsubst⁻ pf Sp Sp₁)
gsubst⁻ pf (∧⁻L₂ Sp) Sp₁ = ∧⁻L₂ (gsubst⁻ pf Sp Sp₁)
-}


