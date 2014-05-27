open import Data.List
open import Data.Empty
open import Data.Sum
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open import Data.List.Any
open import Data.List.All
open import Data.Product
open Membership-≡

open import ListExtra
open import Foc


module FocSimpleProps where



term-⊥-context : ∀{Γ U} → stable U → Pers (↑ ⊥⁺) ∈ Γ  → Term Γ [] U
term-⊥-context pf (here refl) = 
  focL-init pf (focL-step pf (here refl) (focL-end pf (↑L-cons pf (↑L-nil pf ⊥L))) ) 
term-⊥-context pf (there In) = 
  focL-init pf (focL-step pf (there In) (focL-end pf (↑L-cons pf (↑L-nil pf ⊥L))))



{-

ALL THOSE LEMMAS ARE WRONG
C.F. ahmm at the end of this file

value-∧⁺-context : ∀{Γ' Γ A B U} 
  → Value (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) U 
  → Value (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) U 

term-∧⁺-context : ∀{Γ' Γ A B L U} 
  → Term  (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) L U 
  → Term (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) L U 

spine-l-∧⁺-context : ∀{Γ' Γ L- A B U} 
  → Spine-l  (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) L- U 
  → Spine-l (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) L- U 

spine-∧⁺-context : ∀{Γ' Γ L- L+ A B U} 
  → Spine  (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) L- L+ U 
  → Spine (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ) L- L+ U 
-}



------
-------



term-and-notand-absurd :  ∀{Γ Q L+ R}
  → Term Γ L+ (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺)))
  → All (λ x → x ≡ Pers (↑ (a Q ⁺)) ⊎ x ≡ Pers (↑ (a R ⁺)) ⊎  x ≡ HSusp (a Q ⁺)  ⊎  x ≡ HSusp (a R ⁺) ) Γ
  → All (λ x → x ≡ a Q ⁺ ⊎ x ≡ a R ⁺) L+
  → ⊥

spinel-and-notand-absurd : ∀{Γ Q L+ R}
 → Spine-l Γ L+ (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺))) 
 → All (λ x → x ≡ Pers (↑ (a Q ⁺)) ⊎ x ≡ Pers (↑ (a R ⁺))  ⊎  x ≡ HSusp (a Q ⁺)  ⊎  x ≡ HSusp (a R ⁺) ) Γ
 → All (\x → x ≡ (↑ (a Q ⁺)) ⊎ x ≡ (↑ (a R ⁺))) L+
 → ⊥ 

term-and-notand-absurd (η⁺ N) All1 (inj₁ refl ∷ All2) = term-and-notand-absurd N (inj₂ (inj₂ (inj₁ refl)) ∷ All1) All2
term-and-notand-absurd (η⁺ N) All1 (inj₂ refl ∷ All2) = term-and-notand-absurd N (inj₂ (inj₂ (inj₂ refl)) ∷ All1) All2 
term-and-notand-absurd (↓L N) All1 (inj₁ () ∷ All2)
term-and-notand-absurd (↓L N) All1 (inj₂ () ∷ All2)
term-and-notand-absurd ⊥L All1 (inj₁ () ∷ All2)
term-and-notand-absurd ⊥L All1 (inj₂ () ∷ All2)
term-and-notand-absurd (∨L N₁ N₂) All1 (inj₁ () ∷ All2)
term-and-notand-absurd (∨L N₁ N₂) All1 (inj₂ () ∷ All2)
term-and-notand-absurd (⊤⁺L N) All1 (inj₁ () ∷ All2)
term-and-notand-absurd (⊤⁺L N) All1 (inj₂ () ∷ All2)
term-and-notand-absurd (∧⁺L N) All1 (inj₁ () ∷ All2)
term-and-notand-absurd (∧⁺L N) All1 (inj₂ () ∷ All2) 
term-and-notand-absurd (focL-init pf Sp) All1 [] = spinel-and-notand-absurd Sp All1 [] 

spine-and-notand-absurd : ∀{Γ Q L+ L- R}
  → All (λ x → x ≡ Pers (↑ (a Q ⁺)) ⊎ x ≡ Pers (↑ (a R ⁺)) ⊎  x ≡ HSusp (a Q ⁺)  ⊎  x ≡ HSusp (a R ⁺)   ) Γ
  → Spine Γ L+ L- (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺))) 
  → All (\x → x ≡ (↑ (a Q ⁺)) ⊎ x ≡ (↑ (a R ⁺))) L+
  → All (\x → x ≡ a Q ⁺ ⊎ x ≡ a R ⁺) L-
  → ⊥ 
spine-and-notand-absurd All id⁻ (inj₁ () ∷ In1) In2
spine-and-notand-absurd All id⁻ (inj₂ () ∷ In1) In2 
spine-and-notand-absurd All (↑L-cons pf N) (inj₁ refl ∷ In1) In2 = 
  spine-and-notand-absurd All N In1 (all-append (inj₁ refl) In2 )  
spine-and-notand-absurd All (↑L-cons pf N) (inj₂ refl ∷ In1) In2 = 
  spine-and-notand-absurd All N In1 (all-append (inj₂ refl) In2) 
spine-and-notand-absurd {Γ} {Q = Q} {R = R} All (↑L-nil pf N) In1 In2 = 
  term-and-notand-absurd N 
    All
    In2
spine-and-notand-absurd All (⊃L V Sp) (inj₁ () ∷ In1) In2
spine-and-notand-absurd All (⊃L V Sp) (inj₂ () ∷ In1) In2
spine-and-notand-absurd All (∧⁻L₁ Sp) (inj₁ () ∷ In1) In2
spine-and-notand-absurd All (∧⁻L₁ Sp) (inj₂ () ∷ In1) In2
spine-and-notand-absurd All (∧⁻L₂ Sp) (inj₁ () ∷ In1) In2
spine-and-notand-absurd All (∧⁻L₂ Sp) (inj₂ () ∷ In1) In2


spinel-and-notand-absurd (focL-step {A} pf In Sp) In₁ A₁ with lookup In₁ In
spinel-and-notand-absurd (focL-step pf In Sp) In₁ A₁ | inj₁ refl =  
  spinel-and-notand-absurd Sp In₁ (inj₁ refl ∷ A₁) 
spinel-and-notand-absurd (focL-step pf In Sp) In₁ A₁ | inj₂ (inj₁ refl) = 
  spinel-and-notand-absurd Sp In₁ (inj₂ refl ∷ A₁) 
spinel-and-notand-absurd (focL-step pf In Sp) In₁ A₁ | inj₂ (inj₂ (inj₁ ()))
spinel-and-notand-absurd (focL-step pf In Sp) In₁ A₁ | inj₂ (inj₂ (inj₂ ()))
spinel-and-notand-absurd (focL-end pf Sp) In A = 
  spine-and-notand-absurd In Sp A [] 


----
----
----
----









{- *************
 IMPOSSIBILITIES 
-}


-- [weak.agda] weak+-spine-counterex : ∀{Γ Q X} → Spine Γ (a Q ⁻ ∷ []) (X ∷ []) (Susp (a Q ⁻)) → ⊥

-- The following is not true, due to the case where L- = a Q ⁻ 
-- spine-η⁺-adm :  ∀{Γ L- L+ U Q} → Spine (HSusp (a Q ⁺) ∷ Γ) L- L+  U → Spine Γ L- (a Q ⁺ ∷ L+) U

spine-⊥-notadm : ∀{Γ Q L- L+ U} → stable U →  Spine Γ (a Q ⁻ ∷ L-) (⊥⁺ ∷ L+) U → ⊥
spine-⊥-notadm pf ()


init-not-empty : ∀{Γ x Q L+ LA U} → Spine Γ (x ∷ a Q ⁻ ∷ LA) L+ U → ⊥
init-not-empty {L+ = []} (↑L-cons pf ())
init-not-empty {L+ = x ∷ L+} (↑L-cons pf ())
init-not-empty (⊃L V Sp) = init-not-empty Sp
init-not-empty (∧⁻L₁ Sp) = init-not-empty Sp
init-not-empty (∧⁻L₂ Sp) = init-not-empty Sp


{- NOT TRUE, DUE TO THE FOLLOWING REASON
ahmm : ∀{Γ' Γ A B U L- } 
  → Spine-l (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) (↑ (A ∧⁺ B) ∷ L-) U 
  → Spine-l (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ)  L- U 
-}

spinel-and-notand-example-absurd : ∀{Q R} 
  → Spine-l [ Pers (↑ ((a Q ⁺) ∧⁺ (a R ⁺))) ] []  (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺))) 
  → Spine-l (Pers (↑ (a Q ⁺)) ∷ [ Pers (↑ (a R ⁺)) ]) [] (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺))) 
  → ⊥
spinel-and-notand-example-absurd Sp1 Sp2 = 
  spinel-and-notand-absurd Sp2 (inj₁ refl ∷ inj₂ (inj₁ refl) ∷ []) []  

