open import Data.Nat
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Data.Product
open import Data.Empty
open import Data.Sum
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open Membership-≡

open import Foc
open import FocProps
open import ListExtra


module FocSubst where

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
 {!!}
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





suc-foldr-eq : ∀{b} {c} {B : Set b} {C : Set c} (LL : List B) (LA : List C)
  → suc (foldr (λ _ → suc) 0 LL) ≡ suc (foldr (λ _ → suc) 0 LA) 
  → length LL ≡ length LA
suc-foldr-eq [] [] Eq = refl
suc-foldr-eq [] (x ∷ LA) ()
suc-foldr-eq (x ∷ LL) [] ()
suc-foldr-eq (x ∷ LL) (x₁ ∷ LA) Eq with length (x ∷ LL) 
suc-foldr-eq (x ∷ LL) (x₁ ∷ LA) refl | .(suc (foldr (λ _ → suc) 0 LA)) = refl 

suc-fold-[] : ∀{b} {B : Set b} → (L : List B) → suc (foldr (λ _ → suc) 0 L) ≡ suc 0 → L ≡ []
suc-fold-[] [] Eq = refl
suc-fold-[] (x ∷ L) ()

suc-fold-⊥ : ∀{b} {B : Set b} → (L : List B) → suc (foldr (λ _ → suc) 0 L) ≡ 0 → ⊥
suc-fold-⊥ L ()

{- Apply the hypothesis that we can reconstruct x₁ in presence of fuse-gen -}
apply-R-splitting : ∀{U Γ LL L+ RA x₁}  
       → stable U
       → ({LA' : List (Type ⁻)} {L'+ : List (Type ⁺)} {U' : Conc} →
               stable U' →
               Exp Γ (Left (inj₁ (LA' , L'+ ++ RA)) U') →
               Exp Γ (Left (inj₁ (x₁ ∷ LA' , L'+)) U'))
       → Exp Γ (Left (inj₁ (fuse-gen LL (L+ ++ RA))) U)
       → Spine Γ (x₁ ∷ proj₁ (fuse-gen LL L+)) (proj₂ (fuse-gen LL L+)) U
apply-R-splitting {LL = []} pf R Sp = R pf Sp
apply-R-splitting {LL = inj₁ x ∷ LL} {L+ = L+} {RA = RA} pf R Sp  
  rewrite fuse-gen-proj₁ {LL = LL} {L+ = L+} {L'+ = RA} 
          | fuse-gen-proj₂ {LL = LL} {L+ = L+} {RA = RA} 
          | assoc (proj₂ x) (proj₂ (fuse-gen LL L+)) RA = R pf Sp  
apply-R-splitting {LL = inj₂ y ∷ LL} {L+ = L+} {RA = RA} pf R Sp
   rewrite fuse-gen-proj₁ {LL = LL} {L+ = L+} {L'+ = RA} 
          | fuse-gen-proj₂ {LL = LL} {L+ = L+} {RA = RA} 
          | assoc y (proj₂ (fuse-gen LL L+)) RA = R pf Sp   






{- Describe the shape of LAs that we can encounter in gsubst -}
gsubst-more-gen-single-neg-lit : ∀{Γ LL L+ Q U}
  → stable U
  → (LA : List (Type ⁻))
  → All (\x →  Exp Γ (Left (proj₁ x) (Susp (proj₂ x)))) (Data.List.zip LL  LA)
  → length LL ≡ length LA
  → Spine Γ LA L+ U
  → ((a Q ⁻) ∈ LA → LA ≡ [ a Q ⁻ ])
gsubst-more-gen-single-neg-lit pf [] Exps Eq Sp ()
gsubst-more-gen-single-neg-lit pf (._ ∷ LA) Exps Eq Sp (here refl) with Sp
gsubst-more-gen-single-neg-lit pf (._ ∷ .[]) Exps Eq Sp (here refl) | id⁻ = refl
gsubst-more-gen-single-neg-lit pf (x ∷ LA) Exps Eq Sp (there In) = ⊥-elim (spine-cons-neg-lit-absurd Sp In)





⊥⁺-admm : ∀{Γ LL LA L+ U} → 
  stable U → 
  length LL ≡ length LA →
  Spine Γ LA L+ U →
  All (λ x → Exp Γ (Left (proj₁ x) (Susp (proj₂ x)))) (zipWith _,_ LL LA) → 
    Exp Γ (Left (inj₁ (proj₁ (fuse-gen LL L+) , ⊥⁺ ∷ proj₂ (fuse-gen LL L+))) U)

⊥⁺-admm {LL = []} pf Eq Sp Exps = ↑L-nil pf ⊥L
-- We have a spine 
⊥⁺-admm {LL = inj₁ (proj₁ , proj₂) ∷ LL} {[]} pf () Sp Exps
⊥⁺-admm {LL = inj₁ (.(x ∷ []) , .[]) ∷ LL} {x ∷ LA} pf Eq Sp (id⁻ ∷ Exps) = {!!}
⊥⁺-admm {LL = inj₁ (._ , L'+) ∷ LL} {x ∷ LA} pf Eq Sp (↑L-cons pf₁ N ∷ Exps) = {!!}
⊥⁺-admm {LL = inj₁ (.[] , ._) ∷ LL} {x ∷ LA} pf Eq Sp (↑L-nil pf₁ N ∷ Exps) = {!!}
⊥⁺-admm {LL = inj₁ (._ , L'+) ∷ LL} {x ∷ LA} pf Eq Sp (⊃L V Sp₁ ∷ Exps) = {!!}
⊥⁺-admm {LL = inj₁ (._ , L'+) ∷ LL} {x ∷ LA} pf Eq Sp (∧⁻L₁ Sp₁ ∷ Exps) = ∧⁻L₁ (⊥⁺-admm pf {!!} Sp {!!} ) 
⊥⁺-admm {LL = inj₁ (._ , L'+) ∷ LL} {x ∷ LA} pf Eq Sp (∧⁻L₂ Sp₁ ∷ Exps) = {!!}
-- We have a term
⊥⁺-admm {LL = inj₂ [] ∷ LL} {[]} pf () SP Exps
⊥⁺-admm {LL = inj₂ [] ∷ LL} {x ∷ LA} pf Eq Sp1 (focL-init pf₁ Sp2 ∷ Exps) 
  with loading-done Sp2
⊥⁺-admm {Γ} {inj₂ [] ∷ LL} {x ∷ LA} pf Eq Sp1 (focL-init pf₁ Sp2 ∷ Exps) 
  | L' , Sub , Sp' , H = {!unload-all-term ? pf (⊥⁺-admm pf Eq Sp1 (Sp' ∷ Exps)) !}

-- Requires a generalization to unload a Spine even when the positive list is not nil

{-
Exp Γ
(Left
 (inj₁
  ((L' ++ []) ++ proj₁ (fuse-gen LL .L+) ,
   ⊥⁺ ∷
   _Ω_1330 x Sp2 L' Sub Sp' H LL LA pf Eq Sp1 pf₁ Exps ++
   proj₂ (fuse-gen LL .L+)))
 .U)

Exp Γ
      (Left
       (inj₁
        (proj₁ (fuse-gen LL .L+) , ⊥⁺ ∷ .Ω ++ proj₂ (fuse-gen LL .L+)))
       .U)
-}

⊥⁺-admm {LL = inj₂ (x ∷ y) ∷ LL} {[]} pf () Sp Exps
⊥⁺-admm {LL = inj₂ (a Q .⁺ ∷ y) ∷ LL} {A₁ ∷ LA} pf Eq Sp (η⁺ N ∷ Exps) = {!!}
⊥⁺-admm {LL = inj₂ (↓ x ∷ y) ∷ LL} {A₁ ∷ LA} pf Eq Sp (px ∷ Exps) = {!!}
⊥⁺-admm {LL = inj₂ (⊥⁺ ∷ y) ∷ LL} {A₁ ∷ LA} pf Eq Sp (px ∷ Exps) = {!!}
⊥⁺-admm {LL = inj₂ (x ∨ x₁ ∷ y) ∷ LL} {A₁ ∷ LA} pf Eq Sp (px ∷ Exps) = {!!}
⊥⁺-admm {LL = inj₂ (⊤⁺ ∷ y) ∷ LL} {A₁ ∷ LA} pf Eq Sp (px ∷ Exps) = {!!}
⊥⁺-admm {LL = inj₂ (x ∧⁺ x₁ ∷ y) ∷ LL} {A₁ ∷ LA} pf Eq Sp (px ∷ Exps) = {!!}
{-
⊥⁺-admm {LL = inj₂ (x ∷ y) ∷ LL} {a Q .⁻ ∷ .[]} pf Eq id⁻ (px ∷ Exps) 
  rewrite length-cons-nil {X = inj₂ (x ∷ y)} {Y = a Q ⁻} {L = LL} Eq = ↑L-nil tt ⊥L
⊥⁺-admm {LL = inj₂ (x ∷ y) ∷ LL} {↑ x₁ ∷ LA} pf Eq Sp (px ∷ Exps) = {!!}
⊥⁺-admm {LL = inj₂ (x ∷ y) ∷ LL} {x₁ ⊃ x₂ ∷ LA} pf Eq Sp (px ∷ Exps) = {!!}
⊥⁺-admm {LL = inj₂ (x ∷ y) ∷ LL} {⊤⁻ ∷ LA} pf Eq Sp (px ∷ Exps) = {!!}
⊥⁺-admm {LL = inj₂ (x ∷ y) ∷ LL} {x₁ ∧⁻ x₂ ∷ .[]} pf Eq id⁻ (px ∷ Exps) = {!!}
⊥⁺-admm {LL = inj₂ (x ∷ y) ∷ LL} {A ∧⁻ x₂ ∷ LA} pf Eq (∧⁻L₁ Sp) (px ∷ Exps) = {!!}
⊥⁺-admm {LL = inj₂ (x ∷ y) ∷ LL} {A ∧⁻ x₂ ∷ LA} pf Eq (∧⁻L₂ Sp) (px ∷ Exps) = {!!} -}
{-  with ⊥⁺-admm {LL = LL} {L+ = L+} {Ω = Ω ++ x ∷ y} {U = U} pf 
  (length-cons {X = inj₁ (LA , Ω)} {Y = x₁} LL LA Eq) {!!} Exps
... | Z rewrite assoc-cons-append ⊥⁺ Ω (x ∷ y) (proj₂ (fuse-gen LL L+)) = Z -}


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
{-with spine-possib-phases x₁ Sp
gsubst-more-gen {Γ} {._ ∷ LL} pf (x₁ ∷ .[]) (⊥L ∷ Exps) Eq Sp | inj₁ (refl , refl) 
  rewrite suc-fold-[] LL Eq  = ↑L-nil pf ⊥L
gsubst-more-gen {Γ} {._ ∷ LL} pf (x₁ ∷ LA) (⊥L ∷ Exps) Eq Sp 
  | inj₂ (RA , Sp' , R) = {!gsubst-more-gen pf LA Exps ? Sp'!} 
  -- Here it's not possible to use ⊥⁺L admissibility simply because it's not true! -}

gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (∨L N₁ N₂ ∷ Exps) Eq Sp = 
  spine-∨-adm (gsubst-more-gen pf (x₁ ∷ LA) (N₁ ∷ Exps) Eq Sp) (gsubst-more-gen pf (x₁ ∷ LA) (N₂ ∷ Exps) Eq Sp ) 
gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (⊤⁺L N ∷ Exps) Eq Sp = 
 {!!}
gsubst-more-gen {LL = inj₂ (A ∧⁺ B ∷ Ω) ∷ LL} pf (x₁ ∷ LA) (∧⁺L N ∷ Exps) Eq Sp = 
  spine-∧⁺-adm (gsubst-more-gen {LL = inj₂ (A ∷ B ∷ Ω) ∷ LL} pf (x₁ ∷ LA) (N ∷ Exps) Eq Sp)

-----------------------
-- BEGINNING OF ID-
-----------------------
gsubst-more-gen {LL = .(inj₁ (a Q ⁻ ∷ [] , [])) ∷ LL} pf (a Q .⁻ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ 
  with length-cons-nil {X = inj₁ ([ a Q ⁻ ] , [])} {Y = a Q ⁻} {L = LL} Eq  
gsubst-more-gen {Γ} {.(inj₁ ([ a Q ⁻ ] , [])) ∷ .[]} pf (a Q .⁻ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ | refl = id⁻

gsubst-more-gen {LL = .(inj₁ (↑ x₁ ∷ [] , [])) ∷ LL} pf (↑ x₁ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ 
  with length-cons-nil {X = inj₁ ([ ↑ x₁ ] , [])} {Y = ↑ x₁} {L = LL} Eq 
gsubst-more-gen {Γ} {.(inj₁ ([ ↑ x₁ ] , [])) ∷ .[]} pf (↑ x₁ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ | refl = id⁻
gsubst-more-gen {LL = .(inj₁ ([ ↑ x ] , [])) ∷ LL} {L+ = L+} pf (↑ x ∷ L-) (id⁻ ∷ Exps) Eq (↑L-cons pf₁ N) 
  with (gsubst-more-gen pf L- Exps (length-cons {X = inj₁ ([ ↑ x ] , [])} {Y = ↑ x} (LL) (L-) Eq) N)
... | R   rewrite fuse-gen-proj₁ {LL} {L+} {[ x ]} 
                   | fuse-gen-proj₂ {LL} {L+} {[ x ]} 
          = ↑L-cons pf₁ {!!}       -- The rewrites do not work!
-- rewrite fuse-gen-expand {LL} {L+ ++ x ∷ []} | 

gsubst-more-gen {LL = .(inj₁ (x₁ ⊃ x₂ ∷ [] , [])) ∷ LL} pf (x₁ ⊃ x₂ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ 
  with length-cons-nil {X = inj₁ ([ x₁ ⊃ x₂ ] , [])} {Y = x₁ ⊃ x₂} {L = LL} Eq
gsubst-more-gen {Γ} {.(inj₁ ([ x₁ ⊃ x₂ ] , [])) ∷ .[]} pf (x₁ ⊃ x₂ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ | refl = id⁻

gsubst-more-gen {LL = .(inj₁ (x₁ ⊃ B ∷ [] , [])) ∷ LL} pf (x₁ ⊃ B ∷ LA) (id⁻ ∷ Exps) Eq (⊃L V Sp) 
  with spine-possib-phases B Sp 
gsubst-more-gen {Γ} {.(inj₁ ([ x₁ ⊃ B ] , [])) ∷ LL} pf (x₁ ⊃ B ∷ .[]) (id⁻ ∷ Exps) Eq (⊃L V Sp) 
  | inj₁ (refl , refl) rewrite suc-fold-[] LL Eq = ⊃L V Sp
gsubst-more-gen {Γ} {.(inj₁ ([ x₁ ⊃ B ] , [])) ∷ LL} pf (x₁ ⊃ B ∷ LA) (id⁻ ∷ Exps) Eq (⊃L V Sp) 
  | inj₂ (RA , Sp' , R) =  
  ⊃L V (apply-R-splitting {LL = LL} pf R (gsubst-more-gen pf LA Exps (suc-foldr-eq LL LA Eq) Sp'))  

gsubst-more-gen {LL = .(inj₁ (⊤⁻ ∷ [] , [])) ∷ LL} pf (⊤⁻ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ 
  with length-cons-nil {X = inj₁ ([ ⊤⁻ ] , [])} {Y = ⊤⁻} {L = LL} Eq 
gsubst-more-gen {Γ} {.(inj₁ ([ ⊤⁻ ] , [])) ∷ .[]} pf (⊤⁻ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ | refl = id⁻

gsubst-more-gen {LL = .(inj₁ (x₁ ∧⁻ x₂ ∷ [] , [])) ∷ LL} pf (x₁ ∧⁻ x₂ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ 
  with length-cons-nil {X = inj₁ (([ x₁ ∧⁻ x₂ ] , []))} {Y = x₁ ∧⁻ x₂ } {L = LL} Eq 
gsubst-more-gen {Γ} {.(inj₁ ([ x₁ ∧⁻ x₂ ] , [])) ∷ .[]} pf (x₁ ∧⁻ x₂ ∷ .[]) (id⁻ ∷ Exps) Eq id⁻ | refl = id⁻

gsubst-more-gen {LL = .(inj₁ (x₁ ∧⁻ x₂ ∷ [] , [])) ∷ LL} pf (x₁ ∧⁻ x₂ ∷ LA) (id⁻ ∷ Exps) Eq (∧⁻L₁ Sp) 
  with spine-possib-phases x₁ Sp 
gsubst-more-gen {Γ} {.(inj₁ ([ x₁ ∧⁻ x₂ ] , [])) ∷ LL} pf (x₁ ∧⁻ x₂ ∷ .[]) (id⁻ ∷ Exps) Eq (∧⁻L₁ Sp) 
  | inj₁ (refl , refl) rewrite suc-fold-[] LL Eq = ∧⁻L₁ Sp
gsubst-more-gen {Γ} {.(inj₁ ([ x₁ ∧⁻ x₂ ] , [])) ∷ LL} {L+ = L+} {U = U} pf (x₁ ∧⁻ x₂ ∷ LA) (id⁻ ∷ Exps) Eq (∧⁻L₁ Sp) 
  | inj₂ (RA , Sp' , R)   = 
  ∧⁻L₁ (apply-R-splitting {LL = LL} pf R ((gsubst-more-gen pf LA Exps (suc-foldr-eq LL LA Eq) Sp'))) 
 
gsubst-more-gen {LL = .(inj₁ (x₁ ∧⁻ x₂ ∷ [] , [])) ∷ LL} pf (x₁ ∧⁻ x₂ ∷ LA) (id⁻ ∷ Exps) Eq (∧⁻L₂ Sp) 
  with spine-possib-phases x₂ Sp 
gsubst-more-gen {Γ} {.(inj₁ ([ x₁ ∧⁻ x₂ ] , [])) ∷ LL} pf (x₁ ∧⁻ x₂ ∷ .[]) (id⁻ ∷ Exps) Eq (∧⁻L₂ Sp) 
  | inj₁ (refl , refl) rewrite suc-fold-[] LL Eq = ∧⁻L₂ Sp
gsubst-more-gen {Γ} {.(inj₁ ([ x₁ ∧⁻ x₂ ] , [])) ∷ LL} {L+ = L+} {U = U} pf (x₁ ∧⁻ x₂ ∷ LA) (id⁻ ∷ Exps) Eq (∧⁻L₂ Sp) 
  | inj₂ (RA , Sp' , R)   = 
  ∧⁻L₂ (apply-R-splitting {LL = LL} pf R ((gsubst-more-gen pf LA Exps (suc-foldr-eq LL LA Eq) Sp')))  
------------------
-- END OF ID-
-------------------

gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (↑L-cons {L+ = L+} pf₁ N ∷ Exps) Eq Sp = 
  spine-↑-adm {L1 = L+} (gsubst-more-gen pf (x₁ ∷ LA) (N ∷ Exps) Eq Sp)

gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (↑L-nil pf₁ N ∷ Exps) Eq Sp = 
  gsubst-more-gen pf (x₁ ∷ LA) (N ∷ Exps) Eq Sp
gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (⊃L V Sp ∷ Exps) Eq Sp₁ = 
  ⊃L V (gsubst-more-gen pf (x₁ ∷ LA) (Sp ∷ Exps) Eq Sp₁)
gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (∧⁻L₁ Sp ∷ Exps) Eq Sp₁ = 
  ∧⁻L₁  (gsubst-more-gen pf (x₁ ∷ LA) (Sp ∷ Exps) Eq Sp₁) 
gsubst-more-gen {LL = ._ ∷ LL} pf (x₁ ∷ LA) (∧⁻L₂ {L- = L-} {L+ = L+} Sp ∷ Exps) Eq Sp₁ = 
 ∧⁻L₂  (gsubst-more-gen pf (x₁ ∷ LA) (Sp ∷ Exps) Eq Sp₁) 











 
{- This particular case where premisses are only terms.
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
  unload-all-term 
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
-}

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


