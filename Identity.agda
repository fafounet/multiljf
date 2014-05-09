open import Data.List
open import Data.Unit
open import Data.Nat
open import Relation.Binary.PropositionalEquality renaming ([_] to Nil)
open import Data.List.Any
open import Data.List.Any.Properties
open Membership-≡


open import Foc
open import FocSubst
open import Weak


module Identity where

-- didn't find in stdlib...
postulate subseteq-cons : ∀ {b} {B : Set b} {X} → (Γ : List B) → X ∷ [] ⊆ X ∷ Γ



-- Identity expansion

expand⁺ : ∀{A Γ Ω U} → Term (HSusp A ∷ Γ) Ω U → Term Γ (A ∷ Ω) U
expand⁻ : ∀{A Γ} → Term Γ [] (Susp A) → Term Γ [] (Inv A)

expand⁺ {a Q .⁺} N = η⁺ N
expand⁺ {↓ A} {Γ} N = 
  ↓L (
    subst⁺ 
      [] 
      (↓R (expand⁻ (focL-init tt (focL-step tt (here refl) (focL-end tt id⁻))))) 
      (wkex N) 
      refl
    ) 
expand⁺ {⊥⁺} N = ⊥L
expand⁺ {A ∨ A₁} N = 
  ∨L (expand⁺ (subst⁺ [] (∨R₁ (id⁺ (here refl))) (wkex N) refl)) 
    (expand⁺ (subst⁺ [] (∨R₂ (id⁺ (here refl))) (wkex N) refl))
expand⁺ {⊤⁺} N = ⊤⁺L (subst⁺ [] ⊤⁺R N refl)
expand⁺ {A ∧⁺ A₁} N = 
  ∧⁺L (expand⁺ 
        (expand⁺ 
          (subst⁺ [] (∧⁺R (id⁺ (there (here refl))) (id⁺ (here refl))) (wkex (wkex N)) refl)))

expand⁻ {a Q .⁻} N = η⁻ N
expand⁻ {↑ A} N = ↑R (subst⁻ tt N refl (↑L-cons tt (↑L-nil tt (expand⁺ (focR (id⁺ (here refl))))))) 
expand⁻ {A ⊃ A₁} N = 
  ⊃R (expand⁺ (expand⁻ (subst⁻ tt (wken N) refl (⊃L (id⁺ (here refl)) id⁻))))
expand⁻ {⊤⁻} N = ⊤⁻R
expand⁻ {A ∧⁻ A₁} N = 
  ∧⁻R (expand⁻ (subst⁻ tt N refl (∧⁻L₁ id⁻))) (expand⁻ (subst⁻ tt N refl (∧⁻L₂ id⁻)))





pers-in-term : (Γ : Ctx) → (A : Type ⁻) → (Pers A ∈ Γ) → Term Γ [] (Inv A)

pers-in-term Γ (a Q .⁻) In = expand⁻ (focL-init tt (focL-step tt In (focL-end tt id⁻))) 
pers-in-term Γ (↑ A) In = 
  ↑R  (focL-init tt (focL-step tt In (focL-end tt 
                    (↑L-cons tt (↑L-nil tt (expand⁺ (focR (id⁺ (here refl)))))))))
pers-in-term Γ (A₁ ⊃ A₂) In =  
  ⊃R (expand⁺ (expand⁻ (
     focL-init tt (focL-step tt (there In) (focL-end tt (
               ⊃L (id⁺ (here refl)) id⁻)))))) 
pers-in-term Γ ⊤⁻ In = ⊤⁻R
pers-in-term Γ (A ∧⁻ A₁) In =  
  ∧⁻R 
    (expand⁻ (focL-init tt (focL-step tt In (focL-end tt (∧⁻L₁ id⁻)))))
    (expand⁻ (focL-init tt (focL-step tt In (focL-end tt (∧⁻L₂ id⁻))))) 

