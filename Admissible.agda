Cut.agda                                                                                            0000640 0001750 0001750 00000031527 12305331007 012625  0                                                                                                    ustar   fafounet                        fafounet                                                                                                                                                                                                               open import Foc

open import Data.List
open import Data.Product
open import Data.Sum
open import Data.List.All
open import Data.List.Any
open import Data.List.Any.Properties
open import Data.Unit
open import Data.Nat
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])

module Cut where

-- {-# NO_TERMINATION_CHECK #-}
cut⁺ : ∀{U Γ Ω}
  → suspnormalΓ Γ
  → suspnormal U
  → (LAi : List (Type ⁺))
  → All (\x → Value Γ x) LAi
  → Term Γ (LAi ++ Ω) U
  → Term Γ Ω U

cut⁻ : ∀{U Γ N} 
  → suspnormalΓ Γ 
  → suspstable U
  → (LA : List (Type ⁻))
  → (length LA ≡ suc N)
  → All (\x → Term Γ [] (Inv x)) LA
  → All (\x → Spine Γ x U) LA
  → Term Γ [] U

rsubst+  : ∀{Ω Γ Form} (Γ' : Ctx)
  → suspnormalΓ (Γ' ++ Γ)
  → suspnormal Form
  → (LA+ : List (Type ⁺))
  → (LA- : List (Type ⁻))
  → All (\x →  Term (Γ' ++ Γ) [] (Inv x)) LA-
  → All (\x → Value Γ x) LA+
  → Term (Γ' ++ (Data.List.map (\x → Pers x) LA-) ++ Γ) (LA+ ++ Ω) Form
  → Term (Γ' ++ Γ) Ω  Form

postulate rsubst-v : ∀{Γ Form} (Γ' : Ctx)   → suspnormalΓ (Γ' ++ Γ)  → suspnormalF Form  → (LA- : List (Type ⁻))  → All (\x →  Term (Γ' ++ Γ) [] (Inv x)) LA-  → Exp (Γ' ++ (Data.List.map (\x → Pers x) LA-) ++ Γ) Form  → Exp (Γ' ++ Γ) Form



-- {-# NO_TERMINATION_CHECK #-}
--rsubst : ∀{Γ Form A} (Γ' : Ctx)
--  → suspnormalΓ (Γ' ++ Γ)
--  → suspnormalF Form
--  → Term (Γ' ++ Γ) [] (Inv A)
--  → Exp (Γ' ++ (Pers A) ∷ Γ) Form
--  → Exp (Γ' ++ Γ) Form 

lsubst : ∀{Γ U L A} 
  → suspnormalΓ Γ
  → suspstable U
  → Exp Γ (Left L (True A))
  → Term Γ [ A ] U 
  → Exp Γ (Left L U)




-- -- Positive principal substitution

cut⁺ pfΓ pf [] Values T = T

cut⁺ pfΓ pf (z ∷ LA) ((id⁺ v) ∷ Values) N with (pfΓ v)
cut⁺ pfΓ pf (.(a A ⁺) ∷ LA) (id⁺ v ∷ Values) (η⁺ N) | A , refl = 
  subst⁺ [] (a A ⁺ ∷ []) (id⁺ v ∷ []) (cut⁺ (conssusp pfΓ) pf LA (wken-all-rfoc {[]} Values) N)  
cut⁺ {U} {Γ} {Ω} pfΓ pf (.(↓ A) ∷ LA) (↓R N ∷ Values) (↓L {A} N') = 
  rsubst+ [] pfΓ pf LA (A ∷ []) (N ∷ []) Values N'
  -- rsubst+ [] pfΓ pf N (cut⁺ (conspers pfΓ) pf LA (wken-all-rfoc {[]} Values) N₁)
cut⁺ pfΓ pf (.(A ∨ B) ∷ LA) (∨R₁ V ∷ Values) (∨L {A} {B} N₁ N₂) = cut⁺ pfΓ pf (A ∷ LA) (V ∷ Values) N₁
cut⁺ pfΓ pf (.(A ∨ B) ∷ LA) (∨R₂ V ∷ Values) (∨L {A} {B} N₁ N₂) =  cut⁺ pfΓ pf (B ∷ LA) (V ∷ Values) N₂
cut⁺ pfΓ pf (.⊤⁺ ∷ LA) (px ∷ Values) (⊤⁺L N) = cut⁺ pfΓ pf LA Values N
cut⁺ pfΓ pf (A ∧⁺ B ∷ LA) (∧⁺R V₁ V₂ ∷ Values) (∧⁺L N) = cut⁺ pfΓ pf (B ∷ LA) (V₂ ∷ Values) (cut⁺ pfΓ pf ((A ∷ [])) (V₁ ∷ [])  N)

-- -- Negative principle substitution


cut⁻ pfΓ pf [] () LExp LExp' 
cut⁻ pfΓ pf (_ ∷ LA) LL (focL () x Sp ∷ LExp) (px₁ ∷ LExp')

cut⁻ pfΓ pf (a Q .⁻ ∷ LA) LL (η⁻ N₁ ∷ LExp) (id⁻ ∷ LExp') = N₁

cut⁻ pfΓ (proj₁ , ()) (⊤⁻ ∷ LA) LL (⊤⁻R ∷ LExp) (id⁻ ∷ LExp')
cut⁻ pfΓ (proj₁ , ()) (↑ x ∷ LA) LL (↑R N₁ ∷ LExp) (id⁻ ∷ LExp') 
cut⁻ pfΓ (proj₁ , ()) (x ⊃ x₁ ∷ LA) LL (⊃R N₁ ∷ LExp) (id⁻ ∷ LExp')
cut⁻ pfΓ (proj₁ , ()) (x ∧⁻ x₁ ∷ LA) LL (∧⁻R N₁ N₂ ∷ LExp) (id⁻ ∷ LExp')

cut⁻ pfΓ pf (↑ x ∷ LA) LL (↑R N₁ ∷ LExp) (↑L N₂ ∷ LExp') = lsubst pfΓ pf N₁ N₂

cut⁻ pfΓ pf (x ⊃ x₁ ∷ LA) refl (⊃R N₁ ∷ LExp) (⊃L V Sp ∷ LExp') =
  cut⁻ pfΓ pf (x₁ ∷ LA) refl ((cut⁺ pfΓ tt (x ∷ []) (V ∷ []) N₁) ∷ LExp) (Sp ∷ LExp')

cut⁻ pfΓ pf (x ∧⁻ x₁ ∷ LA) refl (∧⁻R N₁ N₂ ∷ LExp) (∧⁻L₁ Sp ∷ LExp') = 
  cut⁻ pfΓ pf (x ∷ LA) refl (N₁ ∷ LExp) (Sp ∷ LExp')

cut⁻ pfΓ pf (x ∧⁻ x₁ ∷ LA) LL (∧⁻R N₁ N₂ ∷ LExp) (∧⁻L₂ Sp ∷ LExp') = 
  cut⁻ pfΓ pf (x₁ ∷ LA) refl (N₂ ∷ LExp) (Sp ∷ LExp')

helper : ∀{Γ LA- A} → 
  All (λ x₂ → Exp (Γ) (Left (inj₁ []) (Inv x₂))) LA- 
  → Any (_≡_ (Pers A)) (Data.List.map Pers LA-)
  → All (λ x₂ → Exp (Γ) (Left (inj₁ []) (Inv x₂))) (A ∷ [])
helper [] () 
helper (px ∷ L) (here refl) = px ∷ []
helper (px ∷ L) (there In) = helper L In

rsubst+ Γ' pfΓ pf [] LA- LT [] (focR V) = focR (rsubst-v Γ' pfΓ tt LA- LT V )
rsubst+ Γ' pfΓ pf [] LA- LT [] (focL pf₁ x Sp) with fromctxGen Γ' (Data.List.map Pers LA-) x
rsubst+ Γ' pfΓ pf [] LA- LT [] (focL {A} pf₁ x Sp) | inj₁ x₁ = 
  cut⁻ pfΓ (pf₁ , pf) (A ∷ []) refl (helper LT x₁) ((rsubst-v Γ' pfΓ pf LA- LT Sp) ∷ [])
rsubst+ Γ' pfΓ pf [] LA- LT [] (focL pf₁ x Sp) | inj₂ y = 
  focL pf₁ y (rsubst-v Γ' pfΓ pf LA- LT Sp )
rsubst+ Γ' pfΓ pf [] LA- LT [] (η⁺ N) = 
  η⁺ (rsubst-v (_ ∷ Γ' ) (conssusp pfΓ) pf LA- (wken-all-inv {[]} LT) N )
rsubst+ Γ' pfΓ pf [] LA- LT [] (↓L N) = 
  ↓L (rsubst-v (_ ∷ Γ' ) (conspers pfΓ) pf LA- (wken-all-inv {[]} LT) N )
rsubst+ Γ' pfΓ pf [] LA- LT [] ⊥L = ⊥L
rsubst+ Γ' pfΓ pf [] LA- LT [] (∨L N₁ N₂) = 
  ∨L (rsubst+ Γ' pfΓ pf [] LA- LT [] N₁) (rsubst+ Γ' pfΓ pf [] LA- LT [] N₂)
rsubst+ Γ' pfΓ pf [] LA- LT [] (⊤⁺L N) = ⊤⁺L (rsubst+ Γ' pfΓ pf [] LA- LT [] N )
rsubst+ Γ' pfΓ pf [] LA- LT [] (∧⁺L N) = ∧⁺L (rsubst+  Γ' pfΓ pf [] LA- LT [] N)
rsubst+ Γ' pfΓ pf [] LA- LT [] (η⁻ N) = η⁻ (rsubst+  Γ' pfΓ pf [] LA- LT [] N)
rsubst+ Γ' pfΓ pf [] LA- LT [] (↑R N) = ↑R (rsubst+  Γ' pfΓ pf [] LA- LT [] N)
rsubst+ Γ' pfΓ pf [] LA- LT [] (⊃R N) = ⊃R (rsubst+  Γ' pfΓ pf [] LA- LT [] N)
rsubst+ Γ' pfΓ pf [] LA- LT [] ⊤⁻R = ⊤⁻R
rsubst+ Γ' pfΓ pf [] LA- LT [] (∧⁻R N₁ N₂) = 
  ∧⁻R (rsubst+  Γ' pfΓ pf [] LA- LT [] N₁) (rsubst+  Γ' pfΓ pf [] LA- LT [] N₂)


rsubst+ Γ' pfΓ pf (↓ x ∷ LA+) LA- LT (id⁺ v ∷ Values) (↓L N) with (pfΓ (++ʳ Γ' v))
... | proj₁ , ()
------------
-- Part which requires a list for negative types
rsubst+ {Ω} {Γ} Γ' pfΓ pf (a Q .⁺ ∷ LA+) LA- LT (id⁺ v ∷ Values) (η⁺ N) = 
  rsubst+ Γ' pfΓ pf LA+ LA- (LT ) Values 
          (cntr (Γ' ++ Data.List.map Pers LA- ++ Γ) (++ʳ Γ' (++ʳ (Data.List.map Pers LA-) v) ) N) 


rsubst+ {Ω} {Γ} Γ' pfΓ pf (↓ x ∷ LA+) LA- LT (↓R N ∷ Values) (↓L N₁) = 
  rsubst+ Γ' pfΓ pf LA+ (x ∷ LA-) ((wk (λ x₂ → ++ʳ Γ' x₂) N) ∷ LT)  Values (exch-cons {Γ'} {Data.List.map Pers LA- ++ Γ} N₁)
--------------
rsubst+ Γ' pfΓ pf (⊥⁺ ∷ LA+) LA- LT (id⁺ v ∷ Values) ⊥L with (pfΓ (++ʳ Γ' v))
... | proj₁ , ()
rsubst+ Γ' pfΓ pf (x ∨ x₁ ∷ LA+) LA- LT (id⁺ v ∷ Values) (∨L N₁ N₂)  with (pfΓ (++ʳ Γ' v))
... | proj₁ , ()
rsubst+ Γ' pfΓ pf (x ∨ x₁ ∷ LA+) LA- LT (∨R₁ V ∷ Values) (∨L N₁ N₂) = rsubst+ Γ' pfΓ pf (x ∷ LA+) LA- LT (V ∷ Values) N₁
rsubst+ Γ' pfΓ pf (x ∨ x₁ ∷ LA+) LA- LT (∨R₂ V ∷ Values) (∨L N₁ N₂) = rsubst+ Γ' pfΓ pf (x₁ ∷ LA+) LA- LT (V ∷ Values) N₂
rsubst+ Γ' pfΓ pf (⊤⁺ ∷ LA+) LA- LT (_ ∷ Values) (⊤⁺L N) =  rsubst+ Γ' pfΓ pf LA+ LA- LT Values N 
rsubst+ Γ' pfΓ pf (x ∧⁺ x₁ ∷ LA+) LA- LT (id⁺ v ∷ Values) (∧⁺L N) with (pfΓ (++ʳ Γ' v))
... | proj₁ , ()
rsubst+ Γ' pfΓ pf (x ∧⁺ x₁ ∷ LA+) LA- LT (∧⁺R V₁ V₂ ∷ Values) (∧⁺L N) = 
  rsubst+ Γ' pfΓ pf (x ∷ x₁ ∷ LA+) LA- LT (V₁ ∷ V₂ ∷ Values) N 




--rsubst-v  Γ' pfΓ pf LA- TS Exp = {!!}








-- 

-- LA+ Version
--



{- rsubst+ Γ' pfΓ pf [] [] LT Values (focR V) = {!!}
rsubst+ Γ' pfΓ pf [] [] LT Values (focL pf₁ x Sp) = {!!}
rsubst+ Γ' pfΓ pf [] [] LT Values (η⁺ N) = {!!}
rsubst+ Γ' pfΓ pf [] [] LT Values (↓L N) = {!!}
rsubst+ Γ' pfΓ pf [] [] LT Values ⊥L = ⊥L
rsubst+ Γ' pfΓ pf [] [] LT Values (∨L N₁ N₂) = {!!}
rsubst+ Γ' pfΓ pf [] [] LT Values (⊤⁺L N) = {!!}
rsubst+ Γ' pfΓ pf [] [] LT Values (∧⁺L N) = {!!}
rsubst+ Γ' pfΓ pf [] [] LT Values (η⁻ N) = {!!}
rsubst+ Γ' pfΓ pf [] [] LT Values (↑R N) = {!!}
rsubst+ Γ' pfΓ pf₁ [] [] LT Values (⊃R N) = {!!}
rsubst+ Γ' pfΓ pf (η⁻ N) [] [] (⊃R N₁) = ⊃R (rsubst+ Γ' pfΓ pf (η⁻ N) [] [] (N₁))
rsubst+ Γ' pfΓ pf (↑R N) [] [] (⊃R N₁) = ⊃R (rsubst+ Γ' pfΓ pf (↑R N) [] [] (N₁))
rsubst+ Γ' pfΓ pf (⊃R N) [] [] (⊃R N₁) = ⊃R (rsubst+ Γ' pfΓ pf (⊃R N) [] [] N₁)
rsubst+ Γ' pfΓ pf ⊤⁻R [] [] (⊃R N) = ⊃R (rsubst+ Γ' pfΓ pf ⊤⁻R [] [] N )
rsubst+ Γ' pfΓ pf (∧⁻R N₁ N₂) [] [] (⊃R N) = ⊃R (rsubst+ Γ' pfΓ pf (∧⁻R N₁ N₂) [] [] N )
rsubst+ Γ' pfΓ pf T [] Values ⊤⁻R = ⊤⁻R
rsubst+ Γ' pfΓ pf T [] Values (∧⁻R N₁ N₂) = {!!}

--rsubst+ Γ' pfΓ pf T (x ∷ LA) (px ∷ Values) Exp = {!!}

rsubst+ Γ' pfΓ pf T (.(a Q ⁺) ∷ LA) (px ∷ Values) (η⁺ {Q} N) = {!!}
rsubst+ Γ' pfΓ pf T (.(↓ A₁) ∷ LA) (id⁺ v ∷ Values) (↓L {A₁} N) with (pfΓ (++ʳ Γ' v))
... | proj₁ , () 
rsubst+ Γ' pfΓ pf T (.(↓ A₁) ∷ LA) (↓R N ∷ Values) (↓L {A₁} N₁) = {!!}
rsubst+ Γ' pfΓ pf T (.⊥⁺ ∷ LA) (id⁺ v ∷ Values) ⊥L with (pfΓ (++ʳ Γ' v))
... | proj₁ , () 
rsubst+ Γ' pfΓ pf T (.(A₁ ∨ B) ∷ LA) (id⁺ v ∷ Values) (∨L {A₁} {B} N₁ N₂) with (pfΓ (++ʳ Γ' v))
... | proj₁ , () 
rsubst+ Γ' pfΓ pf T (.(A₁ ∨ B) ∷ LA) (∨R₁ V ∷ Values) (∨L {A₁} {B} N₁ N₂) = 
  rsubst+ Γ' pfΓ pf T (A₁ ∷ LA) (V ∷ Values) N₁
rsubst+ Γ' pfΓ pf T (.(A₁ ∨ B) ∷ LA) (∨R₂ V ∷ Values) (∨L {A₁} {B} N₁ N₂) = 
  rsubst+  Γ' pfΓ pf T (B ∷ LA) (V ∷ Values) N₂
rsubst+ Γ' pfΓ pf T (.⊤⁺ ∷ LA) (px ∷ Values) (⊤⁺L N) = 
  rsubst+ Γ' pfΓ pf T LA Values N
rsubst+ Γ' pfΓ pf _ (A₁ ∧⁺ B₁ ∷ LA) (id⁺ v ∷ Values) (∧⁺L N) with (pfΓ (++ʳ Γ' v))
... | proj₁ , ()
rsubst+ Γ' pfΓ pf T (A₁ ∧⁺ B ∷ LA) (∧⁺R V₁ V₂ ∷ Values) (∧⁺L N) = 
  rsubst+ Γ' pfΓ pf T (A₁ ∷ B ∷ LA) (V₁ ∷ V₂ ∷ Values) N 
-} 



















---
-- SIMPLE VERSION 

---

{-- Substitution into values
rsubst Γ' pfΓ pf M (id⁺ z) with fromctx Γ' z
rsubst Γ' pfΓ A₂ A₁ (id⁺ z) | inj₁ ()
rsubst Γ' pfΓ M A₁ (id⁺ z) | inj₂ y = id⁺ y
rsubst Γ' pfΓ pf M (↓R N) = ↓R (rsubst Γ' pfΓ pf M N) 
rsubst Γ' pfΓ pf M(∨R₁ V) = ∨R₁ (rsubst Γ' pfΓ pf M V)
rsubst Γ' pfΓ pf M (∨R₂ V) = ∨R₂ (rsubst Γ' pfΓ pf M V)
rsubst Γ' pfΓ pf M ⊤⁺R = ⊤⁺R
rsubst Γ' pfΓ pf M (∧⁺R V₁ V₂) =
  ∧⁺R (rsubst Γ' pfΓ pf M V₁) (rsubst Γ' pfΓ pf M V₂)

-- Substitution into terms
rsubst Γ' pfΓ pf M (focR V) = focR (rsubst Γ' pfΓ pf M V) 
rsubst Γ' pfΓ pf M (focL pf' x' Sp) with fromctx Γ' x'
rsubst Γ' pfΓ pf M (focL {A} pf' x' Sp) | inj₁ refl =  
   cut⁻ pfΓ (pf' , pf) (A ∷ []) refl (M ∷ []) ((rsubst Γ' pfΓ pf M Sp) ∷ []) 
rsubst Γ' pfΓ pf M (focL pf' x' Sp) | inj₂ y = focL pf' y (rsubst Γ' pfΓ pf M Sp) 
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
rsubst Γ' pfΓ pf M (↑L  N) = ↑L (rsubst Γ' pfΓ pf M N)
rsubst Γ' pfΓ pf M (⊃L V Sp) =  ⊃L (rsubst Γ' pfΓ tt M V) (rsubst Γ' pfΓ pf M Sp)
rsubst Γ' pfΓ pf M (∧⁻L₁ Sp) = ∧⁻L₁ (rsubst Γ' pfΓ pf M Sp)
rsubst Γ' pfΓ pf M (∧⁻L₂ Sp) = ∧⁻L₂ (rsubst Γ' pfΓ pf M Sp)
--}




-- -- -- Substitution out of terms
lsubst pfΓ pf (focR {A} V) N = cut⁺ pfΓ (proj₂ pf) (A ∷ []) (V ∷ []) N
lsubst pfΓ pf (focL pf' x Sp) N = focL (proj₁ pf) x (lsubst pfΓ pf Sp N) 
lsubst pfΓ pf (η⁺ M) N = η⁺ (lsubst (conssusp pfΓ) pf M (wken N))
lsubst pfΓ pf (↓L M) N = ↓L (lsubst (conspers pfΓ) pf M (wken N))
lsubst pfΓ pf ⊥L M = ⊥L
lsubst pfΓ pf (∨L M₁ M₂) N = ∨L (lsubst pfΓ pf M₁ N) (lsubst pfΓ pf M₂ N)
lsubst pfΓ pf (⊤⁺L M) N = ⊤⁺L (lsubst pfΓ pf M N)
lsubst pfΓ pf (∧⁺L M) N = ∧⁺L (lsubst pfΓ pf M N)

-- Substitution of of spines
lsubst pfΓ pf (↑L M) N = ↑L (lsubst pfΓ pf M N)
lsubst pfΓ pf (⊃L V Sp) N = ⊃L V (lsubst pfΓ pf Sp N)
lsubst pfΓ pf (∧⁻L₁ Sp) N = ∧⁻L₁ (lsubst pfΓ pf Sp N)
lsubst pfΓ pf (∧⁻L₂ Sp) N = ∧⁻L₂ (lsubst pfΓ pf Sp N)

                                                                                                                                                                         Foc.agda                                                                                            0000640 0001750 0001750 00000031527 12305331007 012601  0                                                                                                    ustar   fafounet                        fafounet                                                                                                                                                                                                               
open import Data.String hiding (_++_)
open import Data.List
open import Data.Unit
open import Data.Nat
open import Data.Empty
open import Data.Fin hiding (_+_)
open import Data.Product
open import Data.Sum
open import Data.Vec hiding (_∈_;[_];_++_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Any
open import Data.List.All
open import Level
open Membership-≡


module Foc where

-- Propositions and polarity

data Polarity : Set where
  ⁺ : Polarity
  ⁻ : Polarity

data Type : Polarity → Set where
  a : (Q : String) (⁼ : Polarity) → Type ⁼
  --
  ↓ : (A : Type ⁻) → Type ⁺
  ⊥⁺ : Type ⁺
  _∨_ : (A B : Type ⁺) → Type ⁺
  ⊤⁺ : Type ⁺
  _∧⁺_ : (A B : Type ⁺) → Type ⁺
  --
  ↑ : (A : Type ⁺) → Type ⁻
  _⊃_ : (A : Type ⁺) (B : Type ⁻) → Type ⁻
  ⊤⁻ : Type ⁻
  _∧⁻_ : (A B : Type ⁻) → Type ⁻

--_⊆_ : ∀{A} → List A → List A → Set
--_⊆_ = LIST.SET.Sub



-- Judgmental infrastructure

data Conc : Set where
  Inv  : (A : Type ⁻) → Conc
  True : (A : Type ⁺) → Conc
  Susp : (A : Type ⁻) → Conc





stable : Conc → Set
stable (Inv A) = ⊥
stable (True A) = ⊤
stable (Susp A) = ⊤

suspnormal : Conc → Set
suspnormal (Inv A) = ⊤
suspnormal (True A) = ⊤
suspnormal (Susp (a Q .⁻)) = ⊤
suspnormal (Susp (↑ A)) = ⊥
suspnormal (Susp (A ⊃ A₁)) = ⊥
suspnormal (Susp ⊤⁻) = ⊥
suspnormal (Susp (A ∧⁻ A₁)) = ⊥

suspstable : Conc -> Set
suspstable U = stable U × suspnormal U

data Hyp : Set where
  HSusp : (A : Type ⁺) → Hyp
  Pers : (A : Type ⁻) → Hyp

Ctx = List Hyp


hsusp-inj : ∀{x y} → HSusp x ≡ HSusp y → x ≡ y
hsusp-inj refl = refl



{- Suspension normality: all suspended propositions are atomic -}
suspnormalΓ : Ctx → Set
suspnormalΓ Γ = ∀{A} → HSusp A Membership-≡.∈ Γ → ∃ λ Q → A ≡ (a Q ⁺)

conssusp : ∀{Γ Q} → suspnormalΓ Γ → suspnormalΓ ((HSusp (a Q ⁺)) ∷ Γ)
conssusp pfΓ (here px) = , hsusp-inj px
conssusp pfΓ (there A₁) = pfΓ A₁

conspers : ∀{Γ A} → suspnormalΓ Γ → suspnormalΓ ((Pers A) ∷ Γ)
conspers pfΓ (here ())
conspers pfΓ  (there B) = pfΓ B




fromctx : ∀{A B Γ} (Γ' : Ctx) → B ∈ (Γ' ++ A ∷ Γ) → (A ≡ B) ⊎ (B ∈ (Γ' ++ Γ))
fromctx [] (here px) = inj₁ (sym px)
fromctx [] (there In) = inj₂ In
fromctx (x ∷ Γ') (here px) = inj₂ (here px)
fromctx (x ∷ Γ') (there In) with fromctx Γ' In
... | inj₁ l = inj₁ l
... | inj₂ r = inj₂ (there r)


fromctxGen : ∀{A} {Γ : Ctx} → (Γ' : Ctx) → (L : Ctx) → A ∈ (Γ' Data.List.++ L Data.List.++ Γ) 
  → (A ∈ L) ⊎ (A ∈ (Γ' Data.List.++ Γ))
fromctxGen [] [] In = inj₂ In
fromctxGen [] (x ∷ L') (here px) = inj₁ (here px)
fromctxGen [] (x ∷ L') (there In) with fromctxGen [] L' In
... | inj₁ l = inj₁ (there l)
... | inj₂ r = inj₂ r
fromctxGen (x ∷ L) L' (here px) = inj₂ (here px)
fromctxGen (x ∷ L) L' (there In) with fromctxGen L L' In 
... | inj₁ l = inj₁ l
... | inj₂ r = inj₂ (there r)


-- Sequent calculus

data SeqForm : Set where
  Rfoc : (A : Type ⁺) → SeqForm
  Left : (L : List (Type ⁺) ⊎ Type ⁻) (U : Conc) → SeqForm 

suspnormalF : SeqForm → Set
suspnormalF (Rfoc A) = ⊤
suspnormalF (Left L U) = suspnormal U

data Exp (Γ : Ctx) : SeqForm → Set

Value : (Γ : Ctx) → Type ⁺ → Set
Value Γ A = Exp Γ (Rfoc A)

Term : (Γ : Ctx) → List (Type ⁺) → Conc → Set
Term Γ Ω U = Exp Γ (Left (inj₁ Ω) U)

Spine : (Γ : Ctx) (A : Type ⁻) (U : Conc) → Set
Spine Γ A U = Exp Γ (Left (inj₂ A) U)

data Exp Γ where

  -- Values
  id⁺ : ∀{A}
    (v : HSusp A ∈ Γ)
    → Value Γ A
  ↓R : ∀{A}
    (N : Term Γ [] (Inv A))
    → Value Γ (↓ A)
  ∨R₁ : ∀{A B}
    (V : Value Γ A)
    → Value Γ (A ∨ B)
  ∨R₂ : ∀{A B}
    (V : Value Γ B)
    → Value Γ (A ∨ B)
  ⊤⁺R : Value Γ ⊤⁺
  ∧⁺R : ∀{A B}
    (V₁ : Value Γ A)
    (V₂ : Value Γ B)
    → Value Γ (A ∧⁺ B)

  -- Terms
  focR : ∀{A} 
    (V : Value Γ A)
    → Term Γ [] (True A)
  focL : ∀{A U} 
    (pf : stable U)
    (x : Pers A ∈ Γ)
    (Sp : Spine Γ A U)
    → Term Γ [] U
  η⁺ : ∀{Q Ω U}
    (N : Term (HSusp (a Q ⁺) ∷ Γ) Ω U)
    → Term Γ (a Q ⁺ ∷ Ω) U
  ↓L : ∀{A Ω U}
    (N : Term (Pers A ∷ Γ) Ω U)
    → Term Γ (↓ A ∷ Ω) U
  ⊥L : ∀{U Ω}
    → Term Γ (⊥⁺ ∷ Ω) U
  ∨L : ∀{A B Ω U}
    (N₁ : Term Γ (A ∷ Ω) U)
    (N₂ : Term Γ (B ∷ Ω) U)
    → Term Γ (A ∨ B ∷ Ω) U
  ⊤⁺L : ∀{U Ω}
    (N : Term Γ Ω U)
    → Term Γ (⊤⁺ ∷ Ω) U
  ∧⁺L : ∀{U Ω A B}
    (N : Term Γ (A ∷ B ∷ Ω) U)
    → Term Γ (A ∧⁺ B ∷ Ω) U
  η⁻ : ∀{Q}
    (N : Term Γ [] (Susp (a Q ⁻)))
    → Term Γ [] (Inv (a Q ⁻))
  ↑R : ∀{A} 
    (N : Term Γ [] (True A))
    → Term Γ [] (Inv (↑ A)) 
  ⊃R : ∀{A B} 
    (N : Term Γ [ A ] (Inv B))
    → Term Γ [] (Inv (A ⊃ B))
  ⊤⁻R : Term Γ [] (Inv ⊤⁻)
  ∧⁻R : ∀{A B}
    (N₁ : Term Γ [] (Inv A))
    (N₂ : Term Γ [] (Inv B))
    → Term Γ [] (Inv (A ∧⁻ B))

  -- Spines
  id⁻ : ∀{A}
    → Spine Γ A (Susp A)
  ↑L : ∀{A U}
    (N : Term Γ [ A ] U)
    → Spine Γ (↑ A) U
  ⊃L : ∀{A B U}
    (V : Value Γ A)
    (Sp : Spine Γ B U) 
    → Spine Γ (A ⊃ B) U
  ∧⁻L₁ : ∀{A B U}
    (Sp : Spine Γ A U)
    → Spine Γ (A ∧⁻ B) U
  ∧⁻L₂ : ∀{A B U}
    (Sp : Spine Γ B U)
    → Spine Γ (A ∧⁻ B) U

-- Weakening

sub-cons-congr : ∀{a} {A : Set a} {x : A} {xs ys : List A}
      → xs ⊆ ys
      → (x ∷ xs) ⊆ (x ∷ ys)
sub-cons-congr H (here px) = here px
sub-cons-congr H (there L) = there (H L) 

sub-wkex : ∀{a} {A : Set a} {x y : A} {xs ys : List A} 
  → (x ∷ xs) ⊆ (x ∷ y ∷ xs)
sub-wkex (here px) = here px
sub-wkex (there H) = there (there H)

sub-cntr : ∀{a} {A : Set a} {x : A} 
       → (xs : List A)
       → x ∈ xs
       → (x ∷ xs) ⊆ xs
sub-cntr xs In (here px) = subst (λ z → Any (_≡_ z) xs) (sym px) In
sub-cntr xs In (there x∷xs) = x∷xs




wk : ∀{Γ Γ' Form} → Γ ⊆ Γ' → Exp Γ Form → Exp Γ' Form

wk θ (id⁺ v) = id⁺ (θ v)
wk θ (↓R N) = ↓R (wk θ N)
wk θ (∨R₁ V) = ∨R₁ (wk θ V)
wk θ (∨R₂ V) = ∨R₂ (wk θ V)
wk θ ⊤⁺R = ⊤⁺R
wk θ (∧⁺R V₁ V₂) = ∧⁺R (wk θ V₁) (wk θ V₂)

wk θ (focR V) = focR (wk θ V)
wk θ (focL pf x Sp) = focL pf (θ x) (wk θ Sp)
wk θ (η⁺ N) = η⁺ (wk (sub-cons-congr θ) N)
wk θ (η⁻ N) = η⁻ (wk θ N)
wk θ (↓L N) = ↓L (wk (sub-cons-congr θ) N)
wk θ (↑R N) = ↑R (wk θ N)
wk θ ⊥L = ⊥L
wk θ (∨L N₁ N₂) = ∨L (wk θ N₁) (wk θ N₂)
wk θ (⊤⁺L N) = ⊤⁺L (wk θ N)
wk θ (∧⁺L N) = ∧⁺L (wk θ N)
wk θ (⊃R N) = ⊃R (wk θ N)
wk θ ⊤⁻R = ⊤⁻R
wk θ (∧⁻R N₁ N₂) = ∧⁻R (wk θ N₁) (wk θ N₂)

wk θ id⁻ = id⁻
wk θ (↑L N) = ↑L (wk θ N)
wk θ (⊃L V Sp) = ⊃L (wk θ V) (wk θ Sp)
wk θ (∧⁻L₁ Sp) = ∧⁻L₁ (wk θ Sp)
wk θ (∧⁻L₂ Sp) = ∧⁻L₂ (wk θ Sp)


wken : ∀{Γ A Form} → Exp Γ Form → Exp (A ∷ Γ) Form
wken = wk (λ {x} → there)


wken-all-rfoc : ∀{Γ' Γ xs B} 
  → All (λ A → Exp (Γ' ++ Γ) (Rfoc A)) xs
  → All (λ A → Exp (B ∷ (Γ' ++ Γ)) (Rfoc A)) xs
wken-all-rfoc [] = []
wken-all-rfoc (px ∷ All) = Data.List.All.map (\x → wken x) (px ∷ All) 


wken-all-inv : ∀{Γ' Γ Ω xs B} 
  → All (λ A → Exp (Γ' ++ Γ) (Left (inj₁ Ω) (Inv A))) xs
  → All (λ A → Exp (B ∷ (Γ' ++ Γ)) (Left (inj₁ Ω) (Inv A))) xs
wken-all-inv [] = []
wken-all-inv (px ∷ All) = Data.List.All.map (\x → wken x) (px ∷ All) 

wkex : ∀{Γ A B Form} → Exp (A ∷ Γ) Form → Exp (A ∷ B ∷ Γ) Form
wkex {Γ} {A} {B} {Form} = wk (sub-wkex {Level.zero} {Hyp} {A} {B} {Γ} {Γ})

wkex2 : ∀{Γ A B C Form} → Exp (A ∷ B ∷ Γ) Form → Exp (A ∷ B ∷ C ∷ Γ) Form
wkex2 {Γ} {A} {B} {Form} = wk (sub-cons-congr (sub-wkex {Level.zero} {Hyp} {B} {Form} {Γ} {Γ}))

cntr : ∀{A Form} → (Γ : Ctx) → A ∈ Γ → Exp (A ∷ Γ) Form → Exp Γ Form
cntr Γ In Exp = wk (sub-cntr Γ In) Exp

postulate exch-cons : ∀{Γ Γ' LA C x} → Term (x ∷ Γ ++ Γ') LA C → Term (Γ ++ x ∷ Γ') LA C

-- Focal substitution


-- I should use a lemma from the stdlib instead
extra : (Γ Γ' : Ctx) → (A : Type ⁺) → (LAi : List (Type ⁺)) 
  → Any (_≡_ (HSusp A)) (Data.List.map HSusp LAi)
  → All (λ A → Exp (Γ' ++ Γ) (Rfoc A)) LAi
  → Exp (Γ' ++ Γ) (Rfoc A)
extra _ _ _ [] () Y
extra Γ Γ' A (x ∷ LAi) (here px) (px₁ ∷ Y) = subst (λ z → Exp (Γ' ++ Γ) (Rfoc z)) (sym (hsusp-inj px)) px₁
extra Γ Γ' A (x ∷ LAi) (there X) (px ∷ Y) = extra Γ Γ' A LAi X Y

no-pers-in-hsusp : ∀{A} (LAi : List (Type ⁺)) →  Any (_≡_ (Pers A)) (Data.List.map HSusp LAi) → ⊥
no-pers-in-hsusp [] ()
no-pers-in-hsusp (x ∷ LAi) (here ())
no-pers-in-hsusp (x ∷ LAi) (there H) = no-pers-in-hsusp LAi H

no-hsusp-in-pers : ∀{A} (LAi : List (Type ⁻)) →  Any (_≡_ (HSusp A)) (Data.List.map Pers LAi) → ⊥
no-hsusp-in-pers [] ()
no-hsusp-in-pers (x ∷ LAi) (here ())
no-hsusp-in-pers (x ∷ LAi) (there H) = no-hsusp-in-pers LAi H


subst⁺ :
  ∀{Γ Form}
  → (Γ' : Ctx)  
  → (LAi : List (Type ⁺))
  → All (\x → Value (Γ' ++ Γ) x) LAi
  → Exp (Γ' ++ Data.List.map (\x → HSusp x) (LAi) ++ Γ) Form 
  → Exp (Γ' ++ Γ) Form
  
subst⁺ Γ' [] PA (id⁺ v) = id⁺ v
subst⁺ {Γ} Γ' (x ∷ LAi) (px ∷ PA) (id⁺ {A} v)
 with  fromctxGen Γ' (Data.List.map (\x → HSusp x) (x ∷ LAi)) v
... | inj₁ (here px₁) = subst (λ z → Exp (Γ' ++ Γ) (Rfoc z)) (sym (hsusp-inj px₁)) px   
... | inj₁ (there L) = extra Γ Γ' A LAi L PA
... | inj₂ R = id⁺ R

subst⁺ Γ' LAi PA (↓R {A} N) = ↓R (subst⁺ Γ' LAi PA N)
subst⁺ Γ' LAi PA (∨R₁ {A} {B} V) = ∨R₁ (subst⁺ Γ' LAi PA V)
subst⁺ Γ' LAi PA (∨R₂ {A} {B} V) = ∨R₂ (subst⁺ Γ' LAi PA V)
subst⁺ Γ' LAi PA ⊤⁺R = ⊤⁺R
subst⁺ Γ' LAi PA (∧⁺R {A} {B} V₁ V₂) = ∧⁺R (subst⁺ Γ' LAi PA V₁) (subst⁺ Γ' LAi PA V₂)
subst⁺ Γ' LAi PA (focR {A} V) = focR (subst⁺ Γ' LAi PA V)
-- focL
subst⁺ Γ' LAi PA (focL {A} {U} pf x Sp) 
   with  fromctxGen Γ' (Data.List.map (\x → HSusp x) LAi) x 
subst⁺ Γ' [] PA (focL pf x Sp) | inj₁ L = focL pf x Sp
subst⁺ Γ' (x ∷ LAi) (px₁ ∷ PA) (focL pf x₁ Sp) | inj₁ (here ())
subst⁺ Γ' (x ∷ LAi) (px ∷ PA) (focL pf x₁ Sp) | inj₁ (there L) = ⊥-elim (no-pers-in-hsusp LAi L) 
subst⁺ Γ' [] PA (focL pf x Sp) | inj₂ R = focL pf R Sp
subst⁺ Γ' (x ∷ LAi) (px ∷ PA) (focL pf x₁ Sp) | inj₂ R = focL pf R (subst⁺ Γ' (x ∷ LAi) (px ∷ PA) Sp)
-- end focL
subst⁺ Γ' .[] [] (η⁺ N) = η⁺ N
subst⁺ {Γ} Γ' .(x ∷ xs) (_∷_ {x} {xs} px PA) (η⁺ {Q} N) = 
  η⁺ (subst⁺ (_ ∷ Γ') (x ∷ xs)  (wken-all-rfoc {Γ'} (px ∷ PA)) N )

subst⁺ Γ' .[] [] (↓L N) = ↓L N
subst⁺ {Γ} Γ' .(x ∷ xs) (_∷_ {x} {xs} px PA) (↓L {A} N) = 
  ↓L (subst⁺ (_ ∷ Γ') (x ∷ xs) (wken-all-rfoc {Γ'} (px ∷ PA)) N)

subst⁺ Γ' LAi PA (⊥L {U} {Ω}) = ⊥L
subst⁺ Γ' LAi PA (∨L {A} {B} {Ω} {U} N₁ N₂) = 
  ∨L (subst⁺ Γ' LAi PA N₁)
     (subst⁺ Γ' LAi PA N₂)
subst⁺ Γ' LAi PA (⊤⁺L {U} {Ω} N) = ⊤⁺L (subst⁺  Γ' LAi PA N)
subst⁺ Γ' LAi PA (∧⁺L {U} {Ω} {A} {B} N) = 
  ∧⁺L (subst⁺ Γ' LAi PA N)
subst⁺ Γ' LAi PA (η⁻ {Q} N) = 
  η⁻ (subst⁺ Γ' LAi PA N)
subst⁺ Γ' LAi PA (↑R {A} N) = 
  ↑R (subst⁺ Γ' LAi PA N)
subst⁺ Γ' LAi PA (⊃R {A} {B} N) = 
  ⊃R (subst⁺ Γ' LAi PA N)
subst⁺ Γ' LAi PA ⊤⁻R = ⊤⁻R
subst⁺ Γ' LAi PA (∧⁻R {A} {B} N₁ N₂) = 
  ∧⁻R (subst⁺ Γ' LAi PA N₁)
      (subst⁺ Γ' LAi PA N₂)
subst⁺ Γ' LAi PA (id⁻ {A}) = id⁻
subst⁺ Γ' LAi PA (↑L {A} {U} N) = 
  ↑L (subst⁺ Γ' LAi PA N)
subst⁺ Γ' LAi PA (⊃L V Sp) = ⊃L (subst⁺ Γ' LAi PA V) (subst⁺ Γ' LAi PA Sp)
subst⁺ Γ' LAi PA (∧⁻L₁ Sp) = ∧⁻L₁ (subst⁺ Γ' LAi PA Sp)
subst⁺ Γ' LAi PA (∧⁻L₂ Sp) = ∧⁻L₂ (subst⁺ Γ' LAi PA Sp)


subst⁻ : ∀{Γ A L U}
  → stable U
  → Exp Γ (Left L (Susp A))
  → Spine Γ A U
  → Exp Γ (Left L U)

subst⁻ pf (focL _ x Sp) Sp' = focL pf x (subst⁻ pf Sp Sp')
subst⁻ pf (η⁺ N) Sp = η⁺ (subst⁻ pf N (wken Sp))
subst⁻ pf (↓L N) Sp = ↓L (subst⁻ pf N (wken Sp))
subst⁻ pf ⊥L Sp = ⊥L
subst⁻ pf (∨L N₁ N₂) Sp = ∨L (subst⁻ pf N₁ Sp) (subst⁻ pf N₂ Sp)
subst⁻ pf (⊤⁺L N) Sp = ⊤⁺L (subst⁻ pf N Sp)
subst⁻ pf (∧⁺L N) Sp = ∧⁺L (subst⁻ pf N Sp)

subst⁻ pf id⁻ Sp = Sp
subst⁻ pf (↑L N) Sp = ↑L (subst⁻ pf N Sp)
subst⁻ pf (⊃L V Sp) Sp' = ⊃L V (subst⁻ pf Sp Sp')
subst⁻ pf (∧⁻L₁ Sp) Sp' = ∧⁻L₁ (subst⁻ pf Sp Sp')
subst⁻ pf (∧⁻L₂ Sp) Sp' = ∧⁻L₂ (subst⁻ pf Sp Sp')

                                                                                                                                                                         Identity.agda                                                                                       0000640 0001750 0001750 00000002162 12305331007 013654  0                                                                                                    ustar   fafounet                        fafounet                                                                                                                                                                                                               
open import Prelude hiding (⊥; ⊤)
open import Foc

module Identity where

-- Identity expansion

expand⁺ : ∀{A Γ Ω U} → Term (Susp A :: Γ) Ω U → Term Γ (A :: Ω) U
expand⁻ : ∀{A Γ} → Term Γ [] (Susp A) → Term Γ [] (Inv A)

expand⁺ {a Q .⁺} N = η⁺ N
expand⁺ {↓ A} N = 
  ↓L (subst⁺ [] (↓R (expand⁻ (focL <> Z id⁻))) (wkex N))
expand⁺ {⊥} N = ⊥L
expand⁺ {A ∨ A₁} N = 
  ∨L (expand⁺ (subst⁺ [] (∨R₁ (id⁺ Z)) (wkex N))) 
    (expand⁺ (subst⁺ [] (∨R₂ (id⁺ Z)) (wkex N)))
expand⁺ {⊤⁺} N = ⊤⁺L (subst⁺ [] ⊤⁺R N)
expand⁺ {A ∧⁺ A₁} N = 
  ∧⁺L (expand⁺ 
        (expand⁺ 
          (subst⁺ [] (∧⁺R (id⁺ (S Z)) (id⁺ Z)) (wkex (wkex N)))))

expand⁻ {a Q .⁻} N = η⁻ N
expand⁻ {↑ A} N = ↑R (subst⁻ <> N (↑L (expand⁺ (focR (id⁺ Z)))))
expand⁻ {A ⊃ A₁} N = 
  ⊃R (expand⁺ (expand⁻ (subst⁻ <> (wken N) (⊃L (id⁺ Z) id⁻))))
expand⁻ {⊤⁻} N = ⊤⁻R
expand⁻ {A ∧⁻ A₁} N = 
  ∧⁻R (expand⁻ (subst⁻ <> N (∧⁻L₁ id⁻))) (expand⁻ (subst⁻ <> N (∧⁻L₂ id⁻)))
                                                                                                                                                                                                                                                                                                                                                                                                              Unfoc.agda                                                                                          0000640 0001750 0001750 00000040105 12305331007 013134  0                                                                                                    ustar   fafounet                        fafounet                                                                                                                                                                                                               
open import Prelude hiding (⊥; ⊤)
open import Foc hiding (Ctx)
open import Admissible hiding (_⊢_)
import Identity
import Cut

module Unfoc where

data Propo : Set where
  a : (Q : String) (⁼ : Polarity) → Propo
  ⊥ : Propo
  _∨_ : (A B : Propo) → Propo
  ⊤ : Propo
  _∧_ : (A B : Propo) → Propo
  _⊃_ : (A B : Propo) → Propo

Ctx = List Propo

-- Sequent Calculus
{- 
  In order to keep ourselves from having to deal with quadratically-many
  vacuous cases in the proof of focalizaiton, this presentation of the
  sequent calculus is factored into three kinds of rules: initial, left,
  and right rules.
-}

data _⊢_ (Γ : Ctx) (C : Propo) : Set
data LD (Γ : Ctx) : Propo → Propo → Set
data RD (Γ : Ctx) : Propo → Set

data _⊢_ Γ C where
  init : ∀{Q ⁼}
    (x : a Q ⁼ ∈ Γ)
    → C ≡ a Q ⁼
    → Γ ⊢ C
  L : ∀{A}
    (x : A ∈ Γ)
    → LD Γ A C
    → Γ ⊢ C
  R : RD Γ C
    → Γ ⊢ C

data LD Γ where
  ⊥L : ∀{C}
    → LD Γ ⊥ C
  ∨L : ∀{A B C}
    (D₁ : (A :: Γ) ⊢ C)
    (D₂ : (B :: Γ) ⊢ C)
    → LD Γ (A ∨ B) C
  ∧L₁ : ∀{A B C}
    (D : (A :: Γ) ⊢ C)
    → LD Γ (A ∧ B) C
  ∧L₂ : ∀{A B C}
    (D : (B :: Γ) ⊢ C)
    → LD Γ (A ∧ B) C
  ⊃L : ∀{A B C}
    (D₁ : Γ ⊢ A)
    (D₂ : (B :: Γ) ⊢ C)
    → LD Γ (A ⊃ B) C

data RD Γ where
  ∨R₁ : ∀{A B}
    (D : Γ ⊢ A)
    → RD Γ (A ∨ B)
  ∨R₂ : ∀{A B}
    (D : Γ ⊢ B)
    → RD Γ (A ∨ B)
  ⊤R : RD Γ ⊤
  ∧R : ∀{A B}
    (D₁ : Γ ⊢ A)
    (D₂ : Γ ⊢ B)    
    → RD Γ (A ∧ B)  
  ⊃R : ∀{A B}
    (D : (A :: Γ) ⊢ B)
    → RD Γ (A ⊃ B)

data SInv (Γ : Ctx) : Ctx × Propo → Set where
  Z : ∀{C}
    (D : Γ ⊢ C)
    → SInv Γ ([] , C)
  S : ∀{A Ψ C}
    (D : SInv (A :: Γ) (Ψ , C))
    → SInv Γ ((A :: Ψ) , C)

dZ : ∀{Γ A} → SInv Γ ([] , A) → Γ ⊢ A
dZ (Z D) = D

dS : ∀{Γ Ψ A B} → SInv Γ ((B :: Ψ) , A) → SInv (B :: Γ) (Ψ , A)
dS (S D) = D

-- Weakening

wk' : ∀{Γ Γ' A} → Γ ⊆ Γ' → Γ ⊢ A → Γ' ⊢ A
wk' θ (init x Refl) = init (θ x) Refl
wk' θ (L x ⊥L) = L (θ x) ⊥L
wk' θ (R (∨R₁ D)) = R (∨R₁ (wk' θ D))
wk' θ (R (∨R₂ D)) = R (∨R₂ (wk' θ D))
wk' θ (L x (∨L D₁ D₂)) = 
  L (θ x) (∨L (wk' (LIST.SET.sub-cons-congr θ) D₁)
             (wk' (LIST.SET.sub-cons-congr θ) D₂))
wk' θ (R ⊤R) = R ⊤R
wk' θ (R (∧R D₁ D₂)) = R (∧R (wk' θ D₁) (wk' θ D₂))
wk' θ (L x (∧L₁ D)) = L (θ x) (∧L₁ (wk' (LIST.SET.sub-cons-congr θ) D))
wk' θ (L x (∧L₂ D)) = L (θ x) (∧L₂ (wk' (LIST.SET.sub-cons-congr θ) D))
wk' θ (R (⊃R D)) = R (⊃R (wk' (LIST.SET.sub-cons-congr θ) D))
wk' θ (L x (⊃L D₁ D₂)) = 
  L (θ x) (⊃L (wk' θ D₁) (wk' (LIST.SET.sub-cons-congr θ) D₂))

wk'' : ∀{Γ Γ' C} → Γ ⊆ Γ' → SInv Γ C → SInv Γ' C
wk'' θ (Z D) = Z (wk' θ D)
wk'' θ (S D) = S (wk'' (LIST.SET.sub-cons-congr θ) D)

wken' : ∀{Γ A C} → Γ ⊢ C → (A :: Γ) ⊢ C
wken' = wk' LIST.SET.sub-wken

wkex' : ∀{Γ A B C} → (A :: Γ) ⊢ C → (A :: B :: Γ) ⊢ C
wkex' = wk' LIST.SET.sub-wkex

wkex2' : ∀{Γ A B C D} → (A :: B :: Γ) ⊢ D → (A :: B :: C :: Γ) ⊢ D
wkex2' = wk' (LIST.SET.sub-cons-congr LIST.SET.sub-wkex)

cntr' : ∀{Γ A C} → A ∈ Γ → (A :: Γ) ⊢ C → Γ ⊢ C
cntr' x = wk' (LIST.SET.sub-cntr x)

wken'' : ∀{Γ A C} → SInv Γ C → SInv (A :: Γ) C
wken'' = wk'' LIST.SET.sub-wken

wkex'' : ∀{Γ A B C} → SInv (A :: Γ) C → SInv (A :: B :: Γ) C
wkex'' = wk'' LIST.SET.sub-wkex

exch'' : ∀{Γ A B C} → SInv (B :: A :: Γ) C → SInv (A :: B :: Γ) C
exch'' = wk'' LIST.SET.sub-exch

exch2'' : ∀{Γ A B C D} → SInv (C :: A :: B :: Γ) D → SInv (A :: B :: C :: Γ) D
exch2'' = wk'' LIST.SET.sub-exch2


-- Erasure

-- There is a small deviation from the Twelf proof and the article here,
-- because we define erasure over all sequents, not just suspension-normal
-- ones.

erase : ∀{⁼} → Type ⁼ → Propo
erase (a Q ⁼) = a Q ⁼
erase (↓ A) = erase A
erase ⊥ = ⊥
erase (A ∨ B) = erase A ∨ erase B
erase ⊤⁺ = ⊤
erase (A ∧⁺ B) = erase A ∧ erase B
erase (↑ A) = erase A
erase (A ⊃ B) = erase A ⊃ erase B
erase ⊤⁻ = ⊤
erase (A ∧⁻ B) = erase A ∧ erase B

erasehyp : (H : Hyp) → Propo
erasehyp (Susp A) = erase A
erasehyp (Pers A) = erase A

eraseΓ : List Hyp → Ctx
eraseΓ = LIST.map erasehyp

eraseU : (U : Conc) → Propo
eraseU (Inv A) = erase A
eraseU (True A) = erase A
eraseU (Susp A) = erase A

eraseseq : (F : SeqForm) → (Ctx × Propo)
eraseseq (Rfoc A) = [] , erase A
eraseseq (Left (Inl Ω) U) = LIST.map erase Ω , eraseU U
eraseseq (Left (Inr A) U) = [ erase A ] , eraseU U

pull : ∀{Γ P} 
  → P ∈ eraseΓ Γ 
  → ∃ λ H → (H ∈ Γ) × (P ≡ erasehyp H)
pull {[]} ()
pull {H :: Γ} Z = H , Z , Refl
pull {_ :: Γ} (S x) with pull x 
... | H , y , refl = H , S y , refl


-- De-focalization

sound : ∀{F Γ} → suspnormalΓ Γ → suspnormalF F
  → Exp Γ F
  → SInv (eraseΓ Γ) (eraseseq F)
sound pfΓ pf (id⁺ z) with pfΓ z
... | (Q , Refl) = Z (init (LIST.in-map erasehyp z) Refl)
sound pfΓ pf (↓R N) = sound pfΓ pf N
sound pfΓ pf (∨R₁ V) = Z (R (∨R₁ (dZ (sound pfΓ pf V))))
sound pfΓ pf (∨R₂ V) = Z (R (∨R₂ (dZ (sound pfΓ pf V))))
sound pfΓ pf ⊤⁺R = Z (R ⊤R)
sound pfΓ pf (∧⁺R V₁ V₂) =
  Z (R (∧R (dZ (sound pfΓ pf V₁)) (dZ (sound pfΓ pf V₂))))
sound pfΓ pf (focR V) = sound pfΓ pf V
sound pfΓ pf (focL pf₁ x Sp) = 
  Z (cntr' (LIST.in-map erasehyp x) (dZ (dS (sound pfΓ pf Sp))))
sound pfΓ pf (η⁺ N) = S (sound (conssusp pfΓ) pf N)
sound pfΓ pf (↓L N) = S (sound (conspers pfΓ) pf N)
sound pfΓ pf ⊥L = S ⊥L'
 where
  ⊥L' : ∀{Ω Γ C}
    → SInv (⊥ :: Γ) (Ω , C)
  ⊥L' {[]} = Z (L Z ⊥L)
  ⊥L' {_ :: Ω} = S (exch'' ⊥L')
sound pfΓ pf (∨L N₁ N₂) = S (∨L' (dS (sound pfΓ pf N₁)) (dS (sound pfΓ pf N₂)))
 where 
  ∨L' : ∀{Ω Γ A B C}
    → SInv (A :: Γ) (Ω , C)
    → SInv (B :: Γ) (Ω , C)
    → SInv ((A ∨ B) :: Γ) (Ω , C)
  ∨L' {[]} (Z D₁) (Z D₂) = Z (L Z (∨L(wkex' D₁) (wkex' D₂)))
  ∨L' {_ :: _} (S D₁) (S D₂) = S (exch'' (∨L' (exch'' D₁) (exch'' D₂)))
sound pfΓ pf (⊤⁺L N) = S (wken'' (sound pfΓ pf N))
sound pfΓ pf (∧⁺L N) = S (∧⁺L' (dS (dS (sound pfΓ pf N))))
 where
  ∧⁺L' : ∀{Ω Γ A B C}
    → SInv (B :: A :: Γ) (Ω , C)
    → SInv ((A ∧ B) :: Γ) (Ω , C)
  ∧⁺L' {[]} (Z D) = Z (L Z (∧L₁ (L (S Z) (∧L₂ (wkex2' D)))))
  ∧⁺L' {x :: Ω} (S D) = S (exch'' (∧⁺L' (exch2'' D)))
sound pfΓ pf (η⁻ N) = sound pfΓ pf N
sound pfΓ pf (↑R N) = sound pfΓ pf N
sound pfΓ pf (⊃R N) = Z (R (⊃R (dZ (dS (sound pfΓ pf N)))))
sound pfΓ pf ⊤⁻R = Z (R ⊤R)
sound pfΓ pf (∧⁻R N₁ N₂) = 
  Z (R (∧R (dZ (sound pfΓ pf N₁)) (dZ (sound pfΓ pf N₂))))
sound {Left ._ (Susp (a Q .⁻))} pfΓ <> id⁻ = S (Z (init Z Refl))
sound {Left ._ (Susp (↑ _))} pfΓ () id⁻
sound {Left ._ (Susp (_ ⊃ _))} pfΓ () id⁻
sound {Left ._ (Susp ⊤⁻)} pfΓ () id⁻
sound {Left ._ (Susp (_ ∧⁻ _))} pfΓ () id⁻
sound pfΓ pf (↑L N) = sound pfΓ pf N
sound pfΓ pf (⊃L V Sp) =  S (Z (L Z (⊃L (wken' (dZ (sound pfΓ <> V)))
                                       (wkex' (dZ (dS (sound pfΓ pf Sp)))))))
sound pfΓ pf (∧⁻L₁ Sp) = S (Z (L Z (∧L₁ (wkex' (dZ (dS (sound pfΓ pf Sp)))))))
sound pfΓ pf (∧⁻L₂ Sp) = S (Z (L Z (∧L₂ (wkex' (dZ (dS (sound pfΓ pf Sp)))))))


-- Focalization

complete : ∀{U Γ} → suspnormalΓ Γ → suspstable U
  → (eraseΓ Γ) ⊢ (eraseU U)
  → Term Γ [] U

-- Focalization of left rules
-- Instead of the "lshifty" lemma we use an inner induction

complete pfΓ pf (L x D) with pull x 
complete {U} {Γ} pfΓ pf (L x D) | Pers A , y , Refl = cntr y (shifty A D)
 where
  shifty : (B : Type ⁻)
    → LD (eraseΓ Γ) (erase B) (eraseU U) 
    → Term (Pers B :: Γ) [] U
  shifty (a Q .⁻) ()
  shifty (↑ (a Q .⁺)) ()
  shifty (↑ (↓ A)) D = u↑↓L (fst pf) (shifty _ D)
  shifty (↑ ⊥) ⊥L = u⊥L (fst pf)
  shifty (↑ (A₁ ∨ A₂)) (∨L D₁ D₂) = 
    u∨L pfΓ pf (complete (conspers pfΓ) pf D₁) (complete (conspers pfΓ) pf D₂)
  shifty (↑ ⊤⁺) ()
  shifty (↑ (A₁ ∧⁺ A₂)) (∧L₁ D₁) =
    u∧⁺L pfΓ pf (wken (complete (conspers pfΓ) pf D₁))
  shifty (↑ (A₁ ∧⁺ A₂)) (∧L₂ D₁) = 
    u∧⁺L pfΓ pf (wkex (complete (conspers pfΓ) pf D₁))
  shifty (A₁ ⊃ A₂) (⊃L D₁ D₂) = 
    u⊃L pfΓ pf (complete pfΓ (<> , <>) D₁) (complete (conspers pfΓ) pf D₂)
  shifty ⊤⁻ ()
  shifty (A₁ ∧⁻ A₂) (∧L₁ D₁) = u∧⁻L₁ pfΓ (snd pf) (complete (conspers pfΓ) pf D₁)
  shifty (A₁ ∧⁻ A₂) (∧L₂ D₁) = u∧⁻L₂ pfΓ (snd pf) (complete (conspers pfΓ) pf D₁)

complete pfΓ pf (L x ()) | Susp (a Q .⁺) , y , Refl
complete pfΓ pf (L x D) | Susp (↓ (a Q .⁻)) , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp (↓ (↑ A)) , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp (↓ (A ⊃ A₁)) , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp (↓ ⊤⁻) , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp (↓ (A ∧⁻ A₁)) , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp ⊥ , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp (A ∨ A₁) , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp ⊤⁺ , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp (A ∧⁺ A₁) , y , Refl with pfΓ y
... | _ , () 

-- Focalization of right rules
-- Instead of the "rshifty" lemma we use an inner induction

complete {True A} {Γ} pfΓ pf (R D) = shifty A D
 where
  shifty : (B : Type ⁺)
    → RD (eraseΓ Γ) (erase B) 
    → Term Γ [] (True B)
  shifty (a Q .⁺) ()
  shifty (↓ (a Q .⁻)) ()
  shifty (↓ (↑ A)) D = u↓↑R (shifty A D)
  shifty (↓ (A₁ ⊃ A₂)) (⊃R D₁) = u⊃R pfΓ (complete (conspers pfΓ) pf D₁)
  shifty (↓ ⊤⁻) ⊤R = u⊤⁻R
  shifty (↓ (A₁ ∧⁻ A₂)) (∧R D₁ D₂) = 
    u∧⁻R pfΓ (complete pfΓ pf D₁) (complete pfΓ pf D₂)
  shifty ⊥ ()
  shifty (A₁ ∨ A₂) (∨R₁ D₁) = u∨R₁ pfΓ (complete pfΓ pf D₁)
  shifty (A₁ ∨ A₂) (∨R₂ D₁) = u∨R₂ pfΓ (complete pfΓ pf D₁)
  shifty ⊤⁺ ⊤R = u⊤⁺R
  shifty (A₁ ∧⁺ A₂) (∧R D₁ D₂) = 
    u∧⁺R pfΓ (complete pfΓ pf D₁) (complete pfΓ pf D₂)

complete {Inv A} pfΓ (() , snd) (R D)
complete {Susp (a _ ._)} _ (_ , _) (R ())
complete {Susp (↑ _)} pfΓ (_ , ()) _
complete {Susp (_ ⊃ _)} pfΓ (_ , ()) _
complete {Susp ⊤⁻} pfΓ (_ , ()) _
complete {Susp (_ ∧⁻ _)} _ (_ , ()) _

-- Focalization of the initial rule
-- This just ends up being a mess of work, mostly just handling all the
-- unsatisfiable patterns

complete {True A} pfΓ pf (init x refl) with pull x 
complete {True A} {Γ} pfΓ pf (init x refl) | Pers B , y , refl' = 
  cntr y (shifty B A refl refl')
 where
  shifty : ∀{Q ⁼} (B : Type ⁻) (A : Type ⁺)
    → erase A ≡ a Q ⁼
    → a Q ⁼ ≡ erase B
    → Term (Pers B :: Γ) [] (True A)
  shifty (↑ (↓ B)) A refl refl' = u↑↓L <> (shifty B A refl refl')
  shifty B (↓ (↑ A)) refl refl' = u↓↑R (shifty B A refl refl')
  shifty (a Q₁ .⁻) (↓ (a .Q₁ .⁻)) Refl Refl = uinit⁻
  shifty (↑ (a Q₁ .⁺)) (a .Q₁ .⁺) Refl Refl = uinit⁺
  shifty (a Q₁ .⁻) (a Q₂ .⁺) () Refl
  shifty (↑ (a Q₁ .⁺)) (↓ (a Q₂ .⁻)) () Refl
  shifty (↑ ⊥) _ _ ()
  shifty (↑ (B₁ ∨ B₂)) _ _ ()
  shifty (↑ ⊤⁺) _ _ ()
  shifty (↑ (B₁ ∧⁺ B₂)) _ _ ()
  shifty (B₁ ⊃ B₂) _ _ ()
  shifty ⊤⁻ _ _ ()
  shifty (B₁ ∧⁻ B₂) _ _ ()
  shifty _ (↓ (A₁ ⊃ A₂)) () _
  shifty _ (↓ ⊤⁻) () _
  shifty _ (↓ (A₁ ∧⁻ A₂)) () _
  shifty _ ⊥ () _
  shifty _ (A₁ ∨ A₂) () _
  shifty _ ⊤⁺ () _
  shifty _ (A₁ ∧⁺ A₂) () _

complete {True A} pfΓ pf (init x refl) | Susp B , y , refl' with pfΓ y
complete {True A} {Γ} pfΓ pf (init x refl) | Susp (a Q .⁺) , y , Refl | nz =
  cntr y (shifty A refl)
 where
  shifty : (B : Type ⁺)
    → erase B ≡ a Q ⁺
    → Term (Susp (a Q ⁺) :: Γ) [] (True B)
  shifty (a .Q .⁺) Refl = uinitsusp⁺
  shifty (↓ (a Q₁ .⁻)) ()
  shifty (↓ (↑ B)) refl' = u↓↑R (shifty B refl')
  shifty (↓ (B ⊃ B₁)) ()
  shifty (↓ ⊤⁻) ()
  shifty (↓ (B ∧⁻ B₁)) ()
  shifty ⊥ ()
  shifty (B ∨ B₁) ()
  shifty ⊤⁺ ()
  shifty (B ∧⁺ B₁) ()

complete {True A} pfΓ pf (init x refl) | Susp (↓ B) , y , refl' | _ , ()
complete {True A} pfΓ pf (init x refl) | Susp ⊥ , y , refl' | _ , ()
complete {True A} pfΓ pf (init x refl) | Susp (B ∨ B₁) , y , refl' | _ , ()
complete {True A} pfΓ pf (init x refl) | Susp ⊤⁺ , y , refl' | _ , ()
complete {True A} pfΓ pf (init x refl) | Susp (B ∧⁺ B₁) , y , refl' | _ , ()

complete {Susp (a Q .⁻)} pfΓ pf (init x Refl) with pull x 
complete {Susp (a Q .⁻)} {Γ} pfΓ pf (init x Refl) | Pers A , y , refl' =
  cntr y (shifty A refl')
 where
  shifty : (B : Type ⁻)
    → a Q ⁻ ≡ erase B
    → Term (Pers B :: Γ) [] (Susp (a Q ⁻))
  shifty (a .Q .⁻) Refl = uinitsusp⁻
  shifty (↑ (↓ B)) D = u↑↓L <> (shifty B D)
  shifty (↑ (a Q₁ .⁺)) ()
  shifty (↑ ⊥) ()
  shifty (↑ (B ∨ B₁)) ()
  shifty (↑ ⊤⁺) ()
  shifty (↑ (B ∧⁺ B₁)) ()
  shifty (B ⊃ B₁) ()
  shifty ⊤⁻ ()
  shifty (B ∧⁻ B₁) ()

complete {Susp (a Q₁ .⁻)} pfΓ pf (init x Refl) | Susp A , y , refl' with pfΓ y
complete {Susp (a Q₁ .⁻)} pfΓ pf (init x Refl) | Susp (a Q .⁺) , y , () | nz 
complete {Susp (a Q .⁻)} pfΓ pf (init x Refl) | Susp (↓ A) , y , _ | _ , ()
complete {Susp (a Q .⁻)} pfΓ pf (init x Refl) | Susp ⊥ , y , _ | _ , ()
complete {Susp (a Q .⁻)} pfΓ pf (init x Refl) | Susp (A ∨ A₁) , y , _ | _ , ()
complete {Susp (a Q .⁻)} pfΓ pf (init x Refl) | Susp ⊤⁺ , y , _ | _ , ()
complete {Susp (a Q .⁻)} pfΓ pf (init x Refl) | Susp (A ∧⁺ A₁) , y , _ | _ , ()

complete {Inv _} _ (() , _) (init _ _) 


-- Partial inverse of erasure

anno : Propo → Type ⁻
anno (a Q ⁺) = ↑ (a Q ⁺)
anno (a Q ⁻) = a Q ⁻
anno ⊥ = ↑ ⊥
anno (A ∨ B) = ↑ (↓ (anno A) ∨ ↓ (anno B))
anno ⊤ = ⊤⁻
anno (A ∧ B) = anno A ∧⁻ anno B
anno (A ⊃ B) = ↓ (anno A) ⊃ anno B 

eqA : (A : Propo) → A ≡ erase (anno A)
eqA (a Q ⁺) = refl
eqA (a Q ⁻) = refl
eqA ⊥ = refl
eqA (A ∨ B) = lem (eqA A) (eqA B)
 where
  lem : ∀{A A' B B'} → A ≡ A' → B ≡ B' → Id {_} {Propo} (A ∨ B) (A' ∨ B')
  lem Refl Refl = refl
eqA ⊤ = refl
eqA (A ∧ B) = lem (eqA A) (eqA B)
 where
  lem : ∀{A A' B B'} → A ≡ A' → B ≡ B' → Id {_} {Propo} (A ∧ B) (A' ∧ B')
  lem Refl Refl = refl
eqA (A ⊃ B) = lem (eqA A) (eqA B)
 where
  lem : ∀{A A' B B'} → A ≡ A' → B ≡ B' → Id {_} {Propo} (A ⊃ B) (A' ⊃ B')
  lem Refl Refl = refl

annoΓ : Ctx → List Hyp
annoΓ = LIST.map (Pers o anno)

eqΓ : (Γ : Ctx) → Γ ≡ eraseΓ (annoΓ Γ)
eqΓ [] = refl
eqΓ (A :: Γ) = LIST.cons-cong (eqA A) (eqΓ Γ)

annonormal : (Γ : Ctx) → suspnormalΓ (annoΓ Γ) 
annonormal [] () 
annonormal (A :: Γ) (S x) = annonormal Γ x

convert : ∀{A A' Γ Γ'} → Γ ≡ Γ' → A ≡ A' → Γ ⊢ A → Γ' ⊢ A'
convert Refl Refl D = D


-- Corollaries of focalization

cut : ∀{P Q Γ} → Γ ⊢ P → (P :: Γ) ⊢ Q → Γ ⊢ Q
cut {P} {Q} {Γ} D E = 
  convert (symm (eqΓ Γ)) (symm (eqA Q)) 
    (dZ (sound (annonormal Γ) <> N))
 where
  N : Term (annoΓ Γ) [] (True (↓ (anno Q)))
  N = Cut.lsubst (annonormal Γ) (<> , <>) 
        (complete (annonormal Γ) (<> , <>) (convert (eqΓ Γ) (eqA P) D))
        (↓L {A = anno P} (complete (conspers (annonormal Γ)) (<> , <>) 
               (convert (eqΓ (P :: Γ)) (eqA Q) E)))

identity : ∀{A Γ} → (A :: Γ) ⊢ A
identity {A} {Γ} = 
  convert (symm (eqΓ (A :: Γ))) (symm (eqA A)) 
    (dZ (sound (annonormal (A :: Γ)) <> N))
 where
  N : Term (Pers (anno A) :: annoΓ Γ) [] (Inv (anno A))
  N = Identity.expand⁻ (focL <> Z id⁻)

                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           