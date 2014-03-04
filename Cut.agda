open import Foc

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

