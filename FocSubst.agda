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

fuse : List (List (Type ⁻) × List (Type ⁺) ⊎ List (Type ⁺))
  → List (Type ⁻) × List (Type ⁺) 
fuse [] = ([] , [])
fuse (inj₁ (L- , L+) ∷ L) with fuse L
... | (R- , R+) = (L- ++ R-) , (L+ ++ R+)
fuse (inj₂ L+ ∷ L)  with fuse L
... | (R- , R+) = R- , (L+ ++ R+)

{- This cannot work either due to the following case (amongst others):
Γ ; A  ,  Ω1  ⊢ <A1> 
--------------------
Γ ; A ∧ B , Ω1 ⊢ <A1>  ...  Γ ; L ⊢ <An>    Γ ; [A1 ... An] ⊢ U
--------------------------------------------------------------

If we apply the i.h. then we get 

Γ ; [Δ2 ... Δn | A , Ω1 , Ξ2 ... Ξn ] ⊢ U

and we are stuck. At least I don't know how to do.



gsubst-term-y : ∀{Γ LL U}
  → stable U
  → (LA : List (Type ⁻))
  → All (\x →  Exp Γ (Left (proj₁ x) (Susp (proj₂ x)))) (Data.List.zip LL  LA)
  → length LL ≡ length LA
  → Spine Γ LA [] U
  → Exp Γ (Left (inj₁ (fuse LL)) U)
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
  unload-all 
    L' 
    pf 
    {!gsubst-term ? ? ? ?!} 
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


