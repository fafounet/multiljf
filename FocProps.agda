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
open import FocWeak

open import NatExtra
open import ListExtra
open import Subset

module FocProps where


load-std : ∀{Γ U} → Spine-l Γ [] U → Term Γ [] U
load-std (focL-step pf In Sp) = focL-init pf (focL-step pf In Sp)
load-std (focL-end pf Sp) = focL-init pf (focL-end pf Sp)



{-
∧-residual-loading : ∀{Γ A B L1 L2 U} → 
 Spine-l (Γ) (L1 ++ A ∧⁻ B ∷ L2) U → 
 Spine-l (Γ) (L1 ++ A ∷ B ∷ L2) U 
∧-residual-loading {L1 = []} (focL-step pf In Sp) = {!!}
∧-residual-loading {L1 = []} (focL-end pf id⁻) = {!!}
∧-residual-loading {L1 = []} (focL-end pf (∧⁻L₁ Sp)) = {!!}
∧-residual-loading {L1 = []} (focL-end pf (∧⁻L₂ Sp)) = {!!}
∧-residual-loading {L1 = x ∷ L1} Sp = {!!}
-}

load-inv-step-adm : ∀{Γ1 Γ2 X L U} 
  → stable U 
  → Spine-l (Γ1 ++ Pers X ∷ Γ2) (X ∷ L) U 
  → Spine-l (Γ1 ++ Pers X ∷ Γ2) (L) U
load-inv-step-adm {Γ1} {X = X} pf Sp = focL-step pf (in-append-cons {X = Pers X} {L1 = Γ1})  Sp


∧-context-adm : ∀{Γ1 Γ2 A B L} 
  → Exp (Γ1 ++ Pers (A ∧⁻ B) ∷ Γ2)  L 
  → Exp (Γ1 ++ Pers A ∷ Pers B ∷ Γ2)  L

postulate
  -- TODO : PROBABLY WRONG!!!!
  ∧-context-loading-adm : ∀{Γ1 Γ2 A B L} 
    → Exp-l (Γ1 ++ Pers (A ∧⁻ B) ∷ Γ2)  L 
    → Exp-l (Γ1 ++ Pers A ∷ Pers B ∷ Γ2)  L
{-∧-context-loading-adm {Γ1} (focL-step pf In Sp) with fromctx Γ1 In
∧-context-loading-adm {Γ1} {Γ2} {A} {B} (focL-step pf In Sp) | inj₁ refl 
  = {!!}
... | inj₂ X = {!!} --focL-step pf {!!} (∧-context-loading-adm Sp)
∧-context-loading-adm {Γ1} (focL-end pf Sp) = focL-end pf (∧-context-adm {Γ1} Sp)
-}

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

{-
 TODO 
unload-all-adm-bis : ∀{Γ X L- L+ U} 
  → (pf : stable U) 
  → Spine Γ L- (X ∷ L+) U 
  → Data.List.map Pers L- ⊆ Γ 
  → Spine Γ [] (X ∷ L+) U 
unload-all-adm-bis {L+ = []} pf (↑L-cons {y} pf₁ N) Sub = 
  cntr-+-[]-spine pf (y) (unload-all-adm-bis pf₁ N (λ {x} z → Sub (there z)) ) (Sub (here refl)) 
unload-all-adm-bis {L+ = []} pf (↑L-nil pf₁ N) Sub = ↑L-nil pf₁ N
unload-all-adm-bis {L+ = []} pf (⊃L V Sp) Sub = {!!}
unload-all-adm-bis {L+ = []} pf (∧⁻L₁ Sp) Sub = 
  -- An immediate recursive call fails
  {!!}
unload-all-adm-bis {L+ = []} pf (∧⁻L₂ Sp) Sub = {!!}
unload-all-adm-bis {L+ = x ∷ L+} pf Sp Sub = {!!}
-}



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









{- 
⊥⁺-admm : ∀{Γ LL LA L+ Ω U} → 
  stable U → 
  length LL ≡ length LA →
  Spine Γ LA L+ U →
  All (λ x → Exp Γ (Left (proj₁ x) (Susp (proj₂ x)))) (zipWith _,_ LL LA) → 
    Exp Γ (Left (inj₁ (proj₁ (fuse-gen LL L+) , ⊥⁺ ∷ Ω ++ proj₂ (fuse-gen LL L+))) U)


⊥⁺-admm {LL = []} pf Eq Sp Exps = ↑L-nil pf ⊥L
-- We have a spine 
⊥⁺-admm {LL = inj₁ (proj₁ , proj₂) ∷ LL} {[]} pf () Sp Exps
⊥⁺-admm {LL = inj₁ (L'- , L'+) ∷ LL} {x ∷ LA} pf Eq Sp (px ∷ Exps) = {!⊥⁺-admm {LL = LL} pf ? Exps!}
-- We have a term
⊥⁺-admm {LL = inj₂ [] ∷ LL} {[]} pf () SP Exps
⊥⁺-admm {LL = inj₂ [] ∷ LL} {x ∷ LA} pf Eq Sp1 (focL-init pf₁ Sp2 ∷ Exps) 
  with loading-done Sp2
⊥⁺-admm {Γ} {inj₂ [] ∷ LL} {x ∷ LA} pf Eq Sp1 (focL-init pf₁ Sp2 ∷ Exps) 
  | L' , Sub , Sp' , H = {!unload-all-term ? pf (⊥⁺-admm pf Eq Sp1 (Sp' ∷ Exps)) !}

-- Requires a generalization to unload a Spine even when the positive list is not nil

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



