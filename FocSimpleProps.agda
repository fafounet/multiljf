open import Data.List
open import Data.Empty
open import Data.Sum
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open import Data.List.Any
open import Data.List.All
open import Data.Product
open Membership-≡

open import Foc


module FocSimpleProps where



term-⊥-context : ∀{Γ U} → stable U → Pers (↑ ⊥⁺) ∈ Γ  → Term Γ [] U
term-⊥-context pf (here refl) = 
  focL-init pf (focL-step pf (here refl) (focL-end pf (↑L-cons pf (↑L-nil pf ⊥L))) ) 
term-⊥-context pf (there In) = 
  focL-init pf (focL-step pf (there In) (focL-end pf (↑L-cons pf (↑L-nil pf ⊥L))))



{-
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

spine-∧⁺-context id⁻ = id⁻
spine-∧⁺-context {Γ'} (↑L-cons pf N) = ↑L-cons pf (spine-∧⁺-context {Γ'}  N) 
spine-∧⁺-context {Γ'} (⊃L V Sp) = ⊃L (value-∧⁺-context {Γ'} V) (spine-∧⁺-context {Γ'} Sp) 
spine-∧⁺-context {Γ'} (∧⁻L₁ Sp) = ∧⁻L₁ (spine-∧⁺-context {Γ'} Sp)
spine-∧⁺-context {Γ'} (∧⁻L₂ Sp) = ∧⁻L₂ (spine-∧⁺-context {Γ'} Sp)
spine-∧⁺-context {Γ'} (↑L-nil pf Sp) = ↑L-nil pf (term-∧⁺-context {Γ'} Sp )





spine-l-∧⁺-context {Γ'} (focL-step pf In Sp) 
  -- Not possible to apply focL-step here
  with fromctx Γ' In 
spine-l-∧⁺-context (focL-step pf In Sp) | inj₁ refl = {!!} --reduces to ahmm below
spine-l-∧⁺-context (focL-step pf In Sp) | inj₂ y = focL-step pf {!!} (spine-l-∧⁺-context Sp) --OK
spine-l-∧⁺-context {Γ'} (focL-end pf T) = focL-end pf (spine-∧⁺-context {Γ'} T)


value-∧⁺-context {Γ'} (id⁺ v) = id⁺ {!!} -- True
value-∧⁺-context {Γ'} (↓R N) = ↓R (term-∧⁺-context {Γ'} N)
value-∧⁺-context {Γ'} (∨R₁ V) = ∨R₁ (value-∧⁺-context {Γ'} V)
value-∧⁺-context {Γ'} (∨R₂ V) = ∨R₂ (value-∧⁺-context {Γ'} V)
value-∧⁺-context {Γ'} ⊤⁺R = ⊤⁺R
value-∧⁺-context {Γ'} (∧⁺R V₁ V₂) = ∧⁺R (value-∧⁺-context {Γ'} V₁) (value-∧⁺-context {Γ'} V₂)


term-∧⁺-context {Γ'} (focR V) = focR (value-∧⁺-context {Γ' = Γ'} V)
term-∧⁺-context {Γ'} (focL-init pf Sp) = focL-init pf (spine-l-∧⁺-context {Γ'} Sp)
term-∧⁺-context {Γ'} (η⁺ {Q} N) = η⁺ (term-∧⁺-context {Γ' = HSusp (a Q ⁺) ∷ Γ'} N)
term-∧⁺-context {Γ'} (↓L {A1} N) = ↓L (term-∧⁺-context {Γ' = Pers A1 ∷ Γ'} N)
term-∧⁺-context  ⊥L = ⊥L
term-∧⁺-context {Γ'} (∨L N₁ N₂) = ∨L (term-∧⁺-context {Γ' = Γ'} N₁) (term-∧⁺-context {Γ'} N₂)
term-∧⁺-context {Γ'} (⊤⁺L N) = ⊤⁺L (term-∧⁺-context {Γ'} N)
term-∧⁺-context {Γ'} (∧⁺L N) = ∧⁺L (term-∧⁺-context {Γ'} N)
term-∧⁺-context {Γ'} (η⁻ N) = η⁻ (term-∧⁺-context {Γ'} N)
term-∧⁺-context {Γ'} (↑R N) = ↑R (term-∧⁺-context {Γ'} N)
term-∧⁺-context {Γ'} (⊃R N) = ⊃R (term-∧⁺-context {Γ'} N)
term-∧⁺-context ⊤⁻R = ⊤⁻R
term-∧⁺-context {Γ'} (∧⁻R N₁ N₂) = ∧⁻R (term-∧⁺-context {Γ'} N₁) (term-∧⁺-context {Γ'} N₂)
-}


------
-------


{-
bbbb : ∀{A B Q R L- } → 
  ({x : Type ⁻} → x ∈ A ∧⁻ B ∷ L- → x ≡ ↑ (a Q ⁺) ⊎ x ≡ ↑ (a R ⁺))
     → ({x : Type ⁻} →
       x ∈ L- → x ≡ ↑ (a Q ⁺) ⊎ x ≡ ↑ (a R ⁺))
bbbb H x with H (there x) 
... | Z = Z

term-and-notand-absurd :  ∀{Γ Q L+ R}
  → Term Γ L+ (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺)))
  → All (λ x → x ≡ Pers (↑ (a Q ⁺)) ⊎ x ≡ Pers (↑ (a R ⁺))) Γ
  → All (λ x → x ≡ a Q ⁺ ⊎ x ≡ a R ⁺) L+
  → ⊥
term-and-notand-absurd (η⁺ N) All1 (inj₁ refl ∷ All2) = {!!}
term-and-notand-absurd (η⁺ N) All1 (inj₂ refl ∷ All2) = {!!}
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
term-and-notand-absurd (focL-init pf Sp) All1 [] = {!!} 

spine-and-notand-absurd : ∀{Q L+ L- R}
 → Spine (Pers (↑ (a Q ⁺)) ∷ [ Pers (↑ (a R ⁺)) ]) L+ L- (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺))) 
 → All (\x → x ≡ (↑ (a Q ⁺)) ⊎ x ≡ (↑ (a R ⁺))) L+
 → All (\x → x ≡ a Q ⁺ ⊎ x ≡ a R ⁺) L-
 → ⊥ 
spine-and-notand-absurd id⁻ (inj₁ () ∷ In1) In2
spine-and-notand-absurd id⁻ (inj₂ () ∷ In1) In2 
spine-and-notand-absurd (↑L-cons pf N) (inj₁ refl ∷ In1) In2 = spine-and-notand-absurd N In1 {!!}  --OK
spine-and-notand-absurd (↑L-cons pf N) (inj₂ refl ∷ In1) In2 = spine-and-notand-absurd N In1 {!!} --OK
spine-and-notand-absurd (↑L-nil pf N) In1 In2 = {!!}
spine-and-notand-absurd (⊃L V Sp) (inj₁ () ∷ In1) In2
spine-and-notand-absurd (⊃L V Sp) (inj₂ () ∷ In1) In2
spine-and-notand-absurd (∧⁻L₁ Sp) (inj₁ () ∷ In1) In2
spine-and-notand-absurd (∧⁻L₁ Sp) (inj₂ () ∷ In1) In2
spine-and-notand-absurd (∧⁻L₂ Sp) (inj₁ () ∷ In1) In2
spine-and-notand-absurd (∧⁻L₂ Sp) (inj₂ () ∷ In1) In2


spinel-and-notand-absurd : ∀{Q L+ R}
 → Spine-l (Pers (↑ (a Q ⁺)) ∷ [ Pers (↑ (a R ⁺)) ]) L+ (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺))) 
 → All (\x → x ≡ (↑ (a Q ⁺)) ⊎ x ≡ (↑ (a R ⁺))) L+
 → ⊥ 
spinel-and-notand-absurd 
  (focL-step pf (here refl) Sp) In₁ = spinel-and-notand-absurd Sp (inj₁ refl ∷ In₁)
spinel-and-notand-absurd 
  (focL-step pf (there (here refl)) Sp) In₁ = spinel-and-notand-absurd Sp (inj₂ refl ∷ In₁)
spinel-and-notand-absurd 
  (focL-step pf (there (there ())) Sp) In₁
spinel-and-notand-absurd 
  (focL-end pf Sp) In = spine-and-notand-absurd Sp In []


spinel-and-notand-example-absurd : ∀{Q R} 
  → Spine-l [ Pers (↑ ((a Q ⁺) ∧⁺ (a R ⁺))) ] [ ↑ ((a Q ⁺) ∧⁺  (a R ⁺)) ]  (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺))) 
  → Spine-l (Pers (↑ (a Q ⁺)) ∷ [ Pers (↑ (a R ⁺)) ]) [] (Susp (↑ (a Q ⁺ ∧⁺ a R ⁺))) 
  → ⊥
spinel-and-notand-example-absurd Sp1 Sp2 = {!!} 


ahmm : ∀{Γ' Γ A B U L- } → Spine-l (Γ' ++ Pers (↑ (A ∧⁺ B)) ∷ Γ) (↑ (A ∧⁺ B) ∷ L-) U → 
  Spine-l (Γ' ++ Pers (↑ A) ∷ Pers (↑ B) ∷ Γ)  L- U 
ahmm (focL-step pf In Sp) = {!!}
ahmm {Γ'} (focL-end pf id⁻)  = {!!} 
  -- Not possible to used focL-end here
--  with fromctx Γ' In 
--... | Z = ? 
ahmm (focL-end pf (↑L-cons pf₁ N)) = {!!}

-}







{- *************
 IMPOSSIBILITIES 
-}


-- [weak.agda] weak+-spine-counterex : ∀{Γ Q X} → Spine Γ (a Q ⁻ ∷ []) (X ∷ []) (Susp (a Q ⁻)) → ⊥

-- The followins is not true, due to the case where L- = a Q ⁻ 
-- spine-η⁺-adm :  ∀{Γ L- L+ U Q} → Spine (HSusp (a Q ⁺) ∷ Γ) L- L+  U → Spine Γ L- (a Q ⁺ ∷ L+) U

spine-⊥-notadm : ∀{Γ Q L- L+ U} → stable U →  Spine Γ (a Q ⁻ ∷ L-) (⊥⁺ ∷ L+) U → ⊥
spine-⊥-notadm pf ()


init-not-empty : ∀{Γ x Q L+ LA U} → Spine Γ (x ∷ a Q ⁻ ∷ LA) L+ U → ⊥
init-not-empty {L+ = []} (↑L-cons pf ())
init-not-empty {L+ = x ∷ L+} (↑L-cons pf ())
init-not-empty (⊃L V Sp) = init-not-empty Sp
init-not-empty (∧⁻L₁ Sp) = init-not-empty Sp
init-not-empty (∧⁻L₂ Sp) = init-not-empty Sp