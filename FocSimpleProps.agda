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