open import Foc
open import Identity


open import Data.String hiding (_++_)
open import Data.List
open import Data.Unit
open import Data.Nat
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Any
open import Data.List.Any.Properties
open import Data.List.All
open Membership-≡

module Cut where



{- WRONG!
  Take A = ↑ ⊥ 
-}
wiik : ∀{Γ A L- L+ U} 
     → suspnormalΓ Γ
     → suspstable U
     → Spine Γ (A ∷ L-) L+ U 
     → (Pers A) ∈ Γ 
     → Spine Γ L- L+ U

enough-conj-l : ∀{Γ A B L- L+ F} 
  → Spine (Pers A ∷ Γ) L- L+ F 
  → Pers (A ∧⁻ B) ∈ Γ 
  → Spine Γ L- L+ F
enough-conj-l Sp In = {!!} 


postulate
  enough-conj-r : ∀{Γ A B L} → Exp (Pers B ∷ Γ) L → Pers (A ∧⁻ B) ∈ Γ → Exp Γ L

postulate
  susp-conj-l : ∀{A B Γ} → suspnormalΓ Γ → Pers (A ∧⁻ B) ∈ Γ →  suspnormalΓ (Pers A ∷ Γ)

postulate
  susp-conj-r : ∀{A B Γ} → suspnormalΓ Γ → Pers (A ∧⁻ B) ∈ Γ →  suspnormalΓ (Pers B ∷ Γ)

--wiik pfΓ st (focL-step pf In Sp) In₁ = focL-step pf In₁ (wiik pfΓ st Sp In)
--wiik pfΓ st (focL-end pf Sp) In = wiik pfΓ st Sp In
wiik pfΓ st id⁻ In = focL-init tt (focL-step tt In (focL-end tt id⁻)) 
wiik pfΓ st (↑L-cons pf N) In = {!wii!} 
     -- focL-step pf In (↑L-cons pf N)
wiik pfΓ st (⊃L V Sp) In = {!!} -- focL-step (proj₁ st) In (⊃L V Sp)
wiik {L- = L-} pfΓ st (∧⁻L₁ Sp) In = enough-conj-l (wiik (susp-conj-l pfΓ In) st (wken Sp) (here refl)) In 
         --cut⁻ pfΓ st L- 
                    --((expand⁻ (focL-init tt (focL-step tt In (focL-end tt (∧⁻L₁ id⁻)))))) Sp
wiik {L- = L-} pfΓ st (∧⁻L₂ Sp) In =  enough-conj-r (wiik (susp-conj-r pfΓ In) st (wken Sp) (here refl)) In  
     --cut⁻ pfΓ st L- 
--((expand⁻ (focL-init tt (focL-step tt In (focL-end tt (∧⁻L₂ id⁻)))))) Sp

-- {-# NO_TERMINATION_CHECK #-}
cut⁺ : ∀{A U Γ Ω}
    → suspnormalΓ Γ
    → suspnormal U
    → Value Γ A
    → Term Γ (A ∷ Ω) U
    → Term Γ Ω U

cut⁻ : ∀{U Γ A}
    → suspnormalΓ Γ
    → suspstable U
    → (LA- : List (Type ⁻))
    → Term Γ [] (Inv A)
    → Spine Γ (A ∷ LA-) [] U
    → Spine Γ LA- [] U

rsubst : ∀{Γ Form A} (Γ' : Ctx)
    → suspnormalΓ (Γ' ++ Γ)
    → suspnormalF Form
    → Term (Γ' ++ Γ) [] (Inv A)
    → Exp (Γ' ++ (Pers A) ∷ Γ) Form
    → Exp (Γ' ++ Γ) Form

{-
postulate 
  lsubst : ∀{Γ U L A} 
    → suspnormalΓ Γ
    → suspstable U
    → Exp Γ (Left L (True A))
    → Term Γ [ A ] U
    → Exp Γ (Left L U)
-}

lsubst' : ∀{Γ U L- L+ L'+ A} 
    → suspnormalΓ Γ
    → suspstable U
    → Spine Γ L- L+ (True A)
    → Term Γ (A ∷ L'+) U
    → Spine Γ L- (L+ ++ L'+) U







-- Positive principal substitution
cut⁺ pfΓ pf (id⁺ x) N with pfΓ x
cut⁺ pfΓ pf (id⁺ x) (η⁺ N) | _ , refl = subst⁺ [] (id⁺ x) N refl
cut⁺ pfΓ pf (id⁺ x) (↑L-nil Y Z)  | _ , refl = cut⁺ pfΓ pf (id⁺ x) Z -- Formula =, part =, derivation <
cut⁺ pfΓ pf (↓R M) (↓L N) = rsubst [] pfΓ pf M N -- Formula <
cut⁺ pfΓ pf (∨R₁ V) (∨L N₁ N₂) = cut⁺ pfΓ pf V N₁
cut⁺ pfΓ pf (∨R₂ V) (∨L N₁ N₂) = cut⁺ pfΓ pf V N₂
cut⁺ pfΓ pf ⊤⁺R (⊤⁺L N) = N
cut⁺ pfΓ pf (∧⁺R V₁ V₂) (∧⁺L N) = cut⁺ pfΓ pf V₂ (cut⁺ pfΓ pf V₁ N)
cut⁺ pfΓ pf V (↑L-nil _ Z) = cut⁺ pfΓ pf V Z


-- Negative principle substitution
{- 
cut⁻ pfΓ pf [] LA+ Ts Sp = Sp
--cut⁻ pfΓ pf (a Q .⁻ ∷ .[]) .[] (focL-init () In Sp ∷ Ts) id⁻
cut⁻ pfΓ pf (a Q .⁻ ∷ .[]) .[] (η⁻ N ∷ Ts) id⁻ = N
cut⁻ pfΓ pf (a Q .⁻ ∷ .[]) .[] (↑L-nil () N ∷ Ts) id⁻
cut⁻ pfΓ (proj₁ , ()) (↑ x ∷ .[]) .[] Ts id⁻
cut⁻ pfΓ (proj₁ , ()) (⊤⁻ ∷ .[]) .[] Ts id⁻ 
cut⁻ pfΓ (proj₁ , ()) (x ∧⁻ x₁ ∷ .[]) .[] Ts id⁻
cut⁻ pfΓ (proj₁ , ()) (x ⊃ x₁ ∷ .[]) .[] Ts id⁻

cut⁻ pfΓ pf (x ∧⁻ x₁ ∷ xs) LA+ (focL () In Sp ∷ Ts) _
cut⁻ pfΓ pf (↑ x ∷ xs) LA+ (focL () In Sp ∷ Ts) _ 
cut⁻ pfΓ pf (x ⊃ x₁ ∷ xs) LA+ (focL () In Sp ∷ Ts) _
cut⁻ pfΓ pf (x ⊃ x₁ ∷ xs) LA+ (↑L-nil () N ∷ Ts) _
cut⁻ pfΓ pf (x ∧⁻ x₁ ∷ xs) LA+ (↑L-nil () N ∷ Ts) _
cut⁻ pfΓ pf (↑ x ∷ xs) LA+ (↑L-nil () N ∷ Ts) (↑L-cons pf₂ N₁) 


cut⁻ pfΓ pf (↑ x ∷ xs) LA+ (↑R N ∷ Ts) (↑L-cons pf₁ N₁) = 
  lsubst' pfΓ (pf₁ , proj₂ pf)  N (cut⁻ pfΓ pf xs (x ∷ LA+) Ts N₁)

cut⁻ pfΓ pf (x ⊃ x₁ ∷ xs) LA+ (⊃R N ∷ Ts) (⊃L V Sp) = 
  cut⁻ pfΓ pf (x₁ ∷ xs) LA+ ((cut⁺ pfΓ tt V N) ∷ Ts) Sp
cut⁻ pfΓ pf (x ∧⁻ x₁ ∷ xs) LA+ (∧⁻R N₁ N₂ ∷ Ts) (∧⁻L₁ Sp) = cut⁻ pfΓ pf (x ∷ xs) LA+ (N₁ ∷ Ts) Sp
cut⁻ pfΓ pf (x ∧⁻ x₁ ∷ xs) LA+ (∧⁻R N₁ N₂ ∷ Ts) (∧⁻L₂ Sp) = cut⁻ pfΓ pf (x₁ ∷ xs) LA+ (N₂ ∷ Ts) Sp

-}

cut⁻ pfΓ pf _ _ _  = {!!}






postulate 
  subseteq-cons-notin : ∀{x L Γ' Γ A}
    → Pers x ∷ Data.List.map Pers L ⊆ Γ' ++ Pers A ∷ Γ 
    → x ≢ A 
    → Pers x ∈ (Γ' ++ Γ)


postulate 
  pff : ∀{x L A Γ Γ'} → (Pers x ∷ L)  ⊆ (Γ' ++ Pers A ∷ Γ)  → (x ≡ A) ⊎ (x ≢ A)


postulate 
  create-simp : ∀{Γ}
              → (L : List (Type ⁻))
              → Data.List.map Pers L ⊆ Γ
              →  All (λ x → Term Γ [] (Inv x)) L
--create-simp [] In = []
--create-simp {Γ} (x ∷ L) In = pers-in-term Γ x (In (here refl))  ∷ (create-simp L (subseteq-drop-cons In))  


postulate 
  create :  ∀{Γ Γ' A} 
            → (L : List (Type ⁻)) 
            → Data.List.map Pers L ⊆ Γ' ++ Pers A ∷ Γ 
            → Term (Γ' ++ Γ) [] (Inv A)
            → All (λ x₁ → Term (Γ' ++ Γ) [] (Inv x₁)) L
--create []  Sub T = []
--create {Γ} {Γ'} {A} (x ∷ L) Sub T with (pff {Γ = Γ} {Γ' = Γ'} Sub)
--create {Γ} {Γ'} (A ∷ L) Sub T | inj₁ refl = T ∷ (create {Γ} {Γ'} L (subseteq-drop-cons Sub) T)
--... | inj₂ Neq = 
--  (pers-in-term (Γ' ++ Γ) x (subseteq-cons-notin {Γ' = Γ'} Sub Neq)) ∷ 
--    (create {Γ} {Γ'} L (subseteq-drop-cons Sub) T)





-- Substitution into values
rsubst Γ' pfΓ pf M (id⁺ z) with fromctx Γ' z
rsubst Γ' pfΓ pf M (id⁺ z) | inj₁ ()
rsubst Γ' pfΓ pf M (id⁺ z) | inj₂ y = id⁺ y
rsubst Γ' pfΓ pf M (↓R N) = ↓R (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M (∨R₁ V) = ∨R₁ (rsubst Γ' pfΓ pf M V)
rsubst Γ' pfΓ pf M (∨R₂ V) = ∨R₂ (rsubst Γ' pfΓ pf M V)
rsubst Γ' pfΓ pf M ⊤⁺R = ⊤⁺R
rsubst Γ' pfΓ pf M (∧⁺R V₁ V₂) =
  ∧⁺R (rsubst Γ' pfΓ pf M V₁) (rsubst Γ' pfΓ pf M V₂)

-- Substitution into terms
rsubst Γ' pfΓ pf M (focR V) = focR (rsubst Γ' pfΓ pf M V)
rsubst Γ' pfΓ pf M (focL-init pf'  Sp) = {!!} --focL-init pf' (rsubst Γ' pfΓ pf M Sp)
--rsubst Γ' pfΓ pf M (focL-step pf' In Sp) with fromctx Γ' In
--rsubst Γ' pfΓ pf M (focL-step {L = L} pf' In Sp) | inj₁ refl = cut⁻ pfΓ (pf' , pf) L M  (rsubst Γ' pfΓ pf M Sp)
--rsubst Γ' pfΓ pf M (focL-step pf' In Sp) | inj₂ y = focL-step pf' y (rsubst Γ' pfΓ pf M Sp) 
--rsubst Γ' pfΓ pf M (focL-end pf'  Sp) = focL-end pf' (rsubst Γ' pfΓ pf M Sp )
rsubst Γ' pfΓ pf M (η⁺ N) = η⁺ (rsubst (_ ∷ Γ') (conssusp pfΓ) pf (wken M) N) 
rsubst Γ' pfΓ pf M (↓L N) = ↓L (rsubst (_ ∷ Γ') (conspers pfΓ) pf (wken M) N) 
rsubst Γ' pfΓ pf M ⊥L = ⊥L
rsubst Γ' pfΓ pf M (∨L N₁ N₂) =
  ∨L (rsubst Γ' pfΓ pf M N₁) (rsubst Γ' pfΓ pf M N₂)
rsubst Γ' pfΓ pf M (⊤⁺L N) = ⊤⁺L (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M (∧⁺L N) = ∧⁺L (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M (η⁻ N) = η⁻ (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M (↑R N) = ↑R (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M (⊃R N) = ⊃R (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M ⊤⁻R = ⊤⁻R
rsubst Γ' pfΓ pf M (∧⁻R N₁ N₂) =
  ∧⁻R (rsubst Γ' pfΓ pf M N₁) (rsubst Γ' pfΓ pf M N₂)

-- Substitution into spines
rsubst Γ' pfΓ pf M id⁻ = id⁻
rsubst Γ' pfΓ pf M (↑L-cons pf' N) = ↑L-cons pf' (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M (↑L-nil pf' N) = ↑L-nil pf' (rsubst Γ' pfΓ pf M N)

rsubst Γ' pfΓ pf M (⊃L V Sp) =
  ⊃L (rsubst Γ' pfΓ tt M V) (rsubst Γ' pfΓ pf M Sp)
rsubst Γ' pfΓ pf M (∧⁻L₁ Sp) = ∧⁻L₁ (rsubst Γ' pfΓ pf M Sp)
rsubst Γ' pfΓ pf M (∧⁻L₂ Sp) = ∧⁻L₂ (rsubst Γ' pfΓ pf M Sp)



lsubst' pfΓ pf (focR V) T = cut⁺ pfΓ (proj₂ pf) V T
lsubst' {Γ} {U} {[]} {[]} {L'+} pfΓ pf (focL-init pf' Sp) T = {!!} -- lsubst' pfΓ pf Sp T
--lsubst' pfΓ pf (focL-step pf' In Sp) T = 
--  {!lsubst' pfΓ pf Sp T!} -- cut⁻ pfΓ pf L L'+ (create-simp L In) (lsubst' pfΓ pf Sp T)
--lsubst' pfΓ pf (focL-end pf' Sp) T = {!!}

lsubst' pfΓ pf (η⁺ N) T = η⁺ (lsubst' (conssusp pfΓ) pf N (wken T))
lsubst' pfΓ pf (↓L N) T = ↓L (lsubst' (conspers pfΓ) pf N ((wken  T))) 
lsubst' pfΓ pf ⊥L T = ⊥L
lsubst' pfΓ pf (∨L N₁ N₂) T = ∨L (lsubst' pfΓ pf N₁ T) (lsubst' pfΓ pf N₂ T)
lsubst' pfΓ pf (⊤⁺L N) T = ⊤⁺L (lsubst' pfΓ pf N T)
lsubst' pfΓ pf (∧⁺L N) T = ∧⁺L (lsubst' pfΓ pf N T)
lsubst' pfΓ pf (↑L-cons pf₁ N) T = ↑L-cons (proj₁ pf) (lsubst' pfΓ pf N T)
lsubst' pfΓ pf (↑L-nil pf₁ N) T = lsubst' pfΓ pf N T
lsubst' pfΓ pf (⊃L V Sp) T = ⊃L V (lsubst' pfΓ pf Sp T)
lsubst' pfΓ pf (∧⁻L₁ Sp) T = ∧⁻L₁ (lsubst' pfΓ pf Sp T)
lsubst' pfΓ pf (∧⁻L₂ Sp) T = ∧⁻L₂ (lsubst' pfΓ pf Sp T)
