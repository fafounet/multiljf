open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open import Data.Product
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.List
open import Data.List.All
open import Data.List.Any
open Membership-≡

open import Foc
open import Weak
open import NatExtra
open import ListExtra
open import Subset

module FocProps where


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


unload-all : ∀{Γ U} 
  → (L : List (Type ⁻)) 
  → (pf : stable U) 
  → Spine Γ L [] U 
  → Data.List.map Pers L ⊆ Γ 
  → Term Γ [] U 
unload-all L- pf Sp In = focL-init pf (unload-all-l L-  pf (focL-end pf Sp) In) 



{-spine-to-term : ∀{Γ Y L- L+ U}
  → (X : Type ⁻)
  → (s : Spine Γ (X ∷ Y ∷ L-) L+ (Susp U))
  → ∃ λ L' → 
     Σ (Term Γ L' (Susp U))  (\s' → height s >′ height s')
spine-to-term {L+} (↑ X) (↑L-cons pf N) = {!!}
spine-to-term (A ⊃ B) (⊃L V Sp) with spine-to-term Sp
... | L' , T, Ieq = ?
spine-to-term (A ∧⁻ B) (∧⁻L₁ Sp) = {!!}
spine-to-term (A ∧⁻ B) (∧⁻L₂ Sp) = {!!}
-}



spine-[]-[] : ∀{Γ U} → Spine Γ [] [] U → ⊥
spine-[]-[]  = λ {Γ} {U} → λ ()

term-[]-⊤ : ∀{Γ} → Term Γ [] (True ⊤⁺)
term-[]-⊤ = λ {Γ} → focR ⊤⁺R

term-⊤ : ∀{Γ} → (L+ : (List (Type ⁺))) → Term Γ L+ (True ⊤⁺) 
term-⊤ [] = focR ⊤⁺R
term-⊤ (x ∷ L+) = weak+-true x (term-⊤ L+)


spine-[]-⊤ : ∀{Γ L+} → (X : Type ⁺) → Spine Γ [] (X ∷ L+) (True ⊤⁺)
spine-[]-⊤ {L+ = L+} X = ↑L-nil tt (term-⊤ (X ∷ L+))


{-
spine-⊤ : ∀{Γ} → (L- : List (Type ⁻)) → (L+ : List (Type ⁺)) → Spine Γ L- L+ (True ⊤⁺)
spine-⊤ = {!!}
 Not true due to the following case, unrelated to multifocusing: -}
counter-ex : ∀{Q} → Spine [] [ a Q ⁻ ] [] (True ⊤⁺) → ⊥ 
counter-ex () 




∧+-inv : ∀{Γ U Ω A B} → Term Γ (A ∧⁺ B ∷ Ω) U → Term Γ (A ∷ B ∷ Ω) U
∧+-inv (∧⁺L N) = N

∨+l-inv : ∀{Γ U Ω A B} → Term Γ (A ∨ B ∷ Ω) U → Term Γ (A ∷ Ω) U
∨+l-inv (∨L N₁ N₂) = N₁

∨+r-inv : ∀{Γ U Ω A B} → Term Γ (A ∨ B ∷ Ω) U → Term Γ (B ∷ Ω) U
∨+r-inv (∨L N₁ N₂) = N₂

⊤+-inv : ∀{Γ U Ω} → Term Γ (⊤⁺ ∷ Ω) U → Term Γ Ω U
⊤+-inv (⊤⁺L N) = N

↓-inv : ∀{Γ A U Ω} → Term Γ (↓ A ∷ Ω) U → Term (Pers A ∷ Γ) Ω U
↓-inv (↓L N) = N

η+-inv : ∀{Γ Q U Ω} → Term Γ (a Q ⁺ ∷ Ω) U → Term (HSusp (a Q ⁺) ∷ Γ) Ω U
η+-inv (η⁺ N) = N


∧+-inv-all : ∀{Γ Ω A B} 
  → (L : List (Type ⁻))
  → All (\x → Term Γ (A ∧⁺ B ∷ Ω) (Susp x)) L
  → All (\x → Term Γ (A ∷ B ∷ Ω) (Susp x)) L
∧+-inv-all [] Ts = []
∧+-inv-all (x ∷ xs) (px ∷ Ts) = (∧+-inv px) ∷ (∧+-inv-all xs Ts)

⊤+-inv-all : ∀{Γ Ω} 
  → (L : List (Type ⁻))
  → All (\x → Term Γ (⊤⁺ ∷ Ω) (Susp x)) L
  → All (\x → Term Γ (Ω) (Susp x)) L
⊤+-inv-all [] Ts = []
⊤+-inv-all (x ∷ xs) (px ∷ Ts) = (⊤+-inv px) ∷ (⊤+-inv-all xs Ts)

∨+l-inv-all : ∀{Γ A B Ω} 
  → (L : List (Type ⁻))
  → All (\x → Term Γ (A ∨ B ∷ Ω) (Susp x)) L
  → All (\x → Term Γ (A ∷ Ω) (Susp x)) L
∨+l-inv-all [] Ts = []
∨+l-inv-all (x ∷ xs) (px ∷ Ts) = (∨+l-inv px) ∷ (∨+l-inv-all xs Ts)

∨+r-inv-all : ∀{Γ A B Ω} 
  → (L : List (Type ⁻))
  → All (\x → Term Γ (A ∨ B ∷ Ω) (Susp x)) L
  → All (\x → Term Γ (B ∷ Ω) (Susp x)) L
∨+r-inv-all [] Ts = []
∨+r-inv-all (x ∷ xs) (px ∷ Ts) = (∨+r-inv px) ∷ (∨+r-inv-all xs Ts)

↓-inv-all : ∀{Γ A Ω} 
  → (L : List (Type ⁻))
  → All (\x → Term Γ (↓ A ∷ Ω) (Susp x)) L
  → All (\x → Term (Pers A ∷ Γ) Ω (Susp x)) L
↓-inv-all [] Ts = []
↓-inv-all (x ∷ xs) (px ∷ Ts) = (↓-inv px) ∷ (↓-inv-all xs Ts)

η+-inv-all : ∀{Γ Q Ω} 
  → (L : List (Type ⁻))
  → All (\x → Term Γ (a Q ⁺ ∷ Ω) (Susp x)) L
  → All (\x → Term (HSusp (a Q ⁺) ∷ Γ) Ω (Susp x)) L
η+-inv-all [] Ts = []
η+-inv-all (x ∷ xs) (px ∷ Ts) = (η+-inv px) ∷ (η+-inv-all xs Ts)

