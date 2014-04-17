open import Data.List
open import Data.List.Any
open import Data.List.Any.Properties
open import Data.List.All
open import Data.Sum
open Membership-≡
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])

open import Foc
open import Subset

module Weak where

wk : ∀{Γ Γ' Form} → Γ ⊆ Γ' → Exp Γ Form → Exp Γ' Form

wk-l : ∀{Γ Γ' Form} → Γ ⊆ Γ' → Exp-l Γ Form → Exp-l Γ' Form

wk-l θ (focL-step pf In Sp) = focL-step pf (θ In) (wk-l θ Sp)
wk-l θ (focL-end pf Sp) = focL-end pf (wk θ Sp) 

wk θ (id⁺ v) = id⁺ (θ v)
wk θ (↓R N) = ↓R (wk θ N)
wk θ (∨R₁ V) = ∨R₁ (wk θ V)
wk θ (∨R₂ V) = ∨R₂ (wk θ V)
wk θ ⊤⁺R = ⊤⁺R
wk θ (∧⁺R V₁ V₂) = ∧⁺R (wk θ V₁) (wk θ V₂)

wk θ (focR V) = focR (wk θ V)
wk θ (focL-init pf Sp ) = focL-init pf (wk-l θ Sp) 
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

wk θ id⁻  = id⁻
wk θ (↑L-nil pf N) = ↑L-nil pf (wk θ N)
wk θ (↑L-cons pf N) = ↑L-cons pf (wk θ N) 
wk θ (⊃L V Sp) = ⊃L (wk θ V) (wk θ Sp)
wk θ (∧⁻L₁ Sp) = ∧⁻L₁ (wk θ Sp)
wk θ (∧⁻L₂ Sp) = ∧⁻L₂ (wk θ Sp)


wken : ∀{Γ A Form} → Exp Γ Form → Exp (A ∷ Γ) Form
wken = wk (λ {x} → there)

wken-list :  ∀{Γ' Γ Form} → Exp Γ Form → Exp (Γ' ++ Γ) Form
wken-list {Γ'} Ex = wk (λ x₁ →  ++ʳ Γ' x₁) Ex

any-middle :  ∀{x y Γ} (Γ' : Ctx) → Any (_≡_ x) (Γ' ++ Γ) → Any (_≡_ x) (Γ' ++ y ∷ Γ)
any-middle [] (here px) = there (here px)
any-middle [] (there A) = there (there A)
any-middle (x₁ ∷ Γ') (here px) = here px
any-middle (x₁ ∷ Γ') (there A) = there (any-middle Γ' A)

any-middle-list :  ∀{x Γ} (Γ' : Ctx) (L : Ctx) → Any (_≡_ x) (Γ' ++ Γ) → Any (_≡_ x) (Γ' ++ L ++ Γ)
any-middle-list Γ' [] A = A
any-middle-list [] L A =  ++ʳ L A
any-middle-list (x₁ ∷ Γ') (x₂ ∷ L) (here refl) = here refl
any-middle-list (x₁ ∷ Γ') (x₂ ∷ L) (there A) = there (any-middle-list  Γ' (x₂ ∷ L) A) 

wken-middle : ∀{Γ Form x } → (Γ' : Ctx) →  Exp (Γ' ++ Γ) Form → Exp (Γ' ++ x ∷ Γ) Form
wken-middle Γ' Ex = wk (λ x₁ → any-middle Γ' x₁) Ex 

wken-middle-list : ∀{Γ Form} → (Γ' : Ctx) → (L : Ctx) → Exp (Γ' ++ Γ) Form → Exp (Γ' ++ L ++ Γ) Form
wken-middle-list Γ' L E = wk (λ x₁ → any-middle-list Γ' L x₁) E



wken-all-rfoc : ∀{Γ' Γ xs B} 
  → All (λ A → Exp (Γ' ++ Γ) (Rfoc A)) xs
  → All (λ A → Exp (B ∷ (Γ' ++ Γ)) (Rfoc A)) xs
wken-all-rfoc [] = []
wken-all-rfoc (px ∷ All) = Data.List.All.map (\x → wken x) (px ∷ All) 


wken-all-inv : ∀{Γ' Γ Ω xs B} 
  → All (λ A → Exp (Γ' ++ Γ) (Left (inj₂ Ω) (Inv A))) xs
  → All (λ A → Exp (B ∷ (Γ' ++ Γ)) (Left (inj₂ Ω) (Inv A))) xs
wken-all-inv [] = []
wken-all-inv (px ∷ All) = Data.List.All.map (\x → wken x) (px ∷ All) 

wkex : ∀{Γ A B Form} → Exp (A ∷ Γ) Form → Exp (A ∷ B ∷ Γ) Form
wkex {Γ} {A} {B} {Form} = wk (sub-wkex  {ys = Γ})

wkex2 : ∀{Γ A B C Form} → Exp (A ∷ B ∷ Γ) Form → Exp (A ∷ B ∷ C ∷ Γ) Form
wkex2 {Γ} {A} {B} {Form} = wk (sub-cons-congr (sub-wkex {ys = Γ}))

cntr : ∀{A Form} → (Γ : Ctx) → A ∈ Γ → Exp (A ∷ Γ) Form → Exp Γ Form
cntr Γ In Exp = wk (sub-cntr Γ In) Exp


{- The following is not true:

spine-cntr : ∀{Γ A L U} 
  → (L' : List (Type ⁻)) 
  → Exp Γ (Left (L' ++ A ∷ L , []) U) 
  → Pers A ∈ Γ 
  → Exp Γ (Left (L' ++ L , []) U) 

For instance if L' = ⊥, L = []

However one could say that either the inversion phase ends with a ⊥L 
or the lemma above is true

Don't forget that the current inversion phase cannot end with a initial negative
rule.

True ??:
spine-cntr : ∀{Γ A L U} 
  → (L' : List (Type ⁻)) 
  → Exp Γ (Left (L' ++ A ∷ L , []) U) 
  → Pers A ∈ Γ 
  → ⊥ ∈ (L' ++ L) ⊎ Exp Γ (Left (L' ++ L , []) U) 

There should be another inversion phase above since this one cannot end.
This means that we don't have to focus now on A since we can do it later.


Remember that

Γ ; [L |] |- U

does not imply that L ⊂ Γ (even if ⊥ ∉ Γ)

Think for instance of 
----------------
 ; [A |] |- <A>
---------------
; [A /\ B |] |- <A> 


-}



weak+-true : ∀{Γ F L+} → (X : Type ⁺) → Term Γ L+ (True F) → Term Γ (X ∷ L+) (True F)
weak+-true (a Q .⁺) T = η⁺ (wken T)
weak+-true (↓ X) T = ↓L (wken T)
weak+-true ⊥⁺ T = ⊥L
weak+-true (X ∨ X₁) T = ∨L (weak+-true X T) (weak+-true X₁ T)
weak+-true ⊤⁺ T = ⊤⁺L T
weak+-true (X ∧⁺ X₁) T = ∧⁺L (weak+-true X (weak+-true X₁ T))

weak+-[]-true : ∀{Γ F} → (L+ :(List (Type ⁺))) →  Term Γ [] (True F) → Term Γ L+ (True F)
weak+-[]-true [] T = T
weak+-[]-true (x ∷ L+) T = weak+-true x (weak+-[]-true L+ T)
