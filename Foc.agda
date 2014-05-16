open import Data.String hiding (_++_)
open import Data.List
open import Data.Unit
open import Data.Nat  hiding (_≤′_; module _≤′_; _<′_; _≥′_; _>′_)
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open import Data.List.Any
open import Data.List.Any.Properties
open import Data.List.All
open import Data.List.Properties
open import Function.Inverse hiding (sym)
open Membership-≡

open import Subset
open import NatExtra
open import ListExtra

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

size-formula : ∀{p} → (Type p) → ℕ 
size-formula (a Q ⁼) = 1
size-formula (↓ x) = 1 + size-formula x
size-formula ⊥⁺ = 1
size-formula (x ∨ x₁) = 1 + size-formula x + size-formula x₁
size-formula ⊤⁺ = 1
size-formula (x ∧⁺ x₁) = 1 + size-formula x + size-formula x₁
size-formula (↑ x) = 1 + size-formula x
size-formula (x ⊃ x₁) = 1 + size-formula x + size-formula x₁
size-formula ⊤⁻ = 1
size-formula (x ∧⁻ x₁) = 1 + size-formula x + size-formula x₁

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

postulate suspnormalsplitleft : ∀{Γ' Γ} → suspnormalΓ (Γ' ++ Γ) → suspnormalΓ Γ'
postulate suspnormalsplitright : ∀{Γ' Γ} → suspnormalΓ (Γ' ++ Γ) → suspnormalΓ Γ

postulate suspnormalconc : ∀{Γ Γ'} → suspnormalΓ Γ → suspnormalΓ Γ' → suspnormalΓ (Γ ++ Γ')


conssusp : ∀{Γ Q} → suspnormalΓ Γ → suspnormalΓ ((HSusp (a Q ⁺)) ∷ Γ)
conssusp pfΓ (here px) = , hsusp-inj px
conssusp pfΓ (there A₁) = pfΓ A₁

conspers : ∀{Γ A} → suspnormalΓ Γ → suspnormalΓ ((Pers A) ∷ Γ)
conspers pfΓ (here ())
conspers pfΓ  (there B) = pfΓ B

concpers : ∀{Γ} → (LA : List (Type ⁻)) → suspnormalΓ Γ → suspnormalΓ (Data.List.map Pers LA ++ Γ)
concpers [] pfΓ = pfΓ
concpers (x ∷ LA) pfΓ = conspers (concpers LA pfΓ)

concconcpers : ∀{Γ} (Γ' : Ctx) (LA : List (Type ⁻))
  → suspnormalΓ (Γ' ++ Γ) 
  →  suspnormalΓ (Γ' ++ Data.List.map Pers LA ++ Γ)
concconcpers {Γ} Γ' LA pfΓ = 
  suspnormalconc (suspnormalsplitleft {Γ'} {Γ} pfΓ) (concpers LA (suspnormalsplitright {Γ'} {Γ} pfΓ))




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
  {- We don't factorize with just two lists because this leads to 
  unwanted conversions -}
  Left : (List (Type ⁻) × List (Type ⁺)) ⊎  List (Type ⁺) → (U : Conc) → SeqForm 

suspnormalF : SeqForm → Set
suspnormalF (Rfoc A) = ⊤
suspnormalF (Left L U) = suspnormal U

data Exp (Γ : Ctx) : SeqForm → Set


Value : (Γ : Ctx) → Type ⁺ → Set
Value Γ A = Exp Γ (Rfoc A)
  
Term : (Γ : Ctx) → List (Type ⁺) → Conc → Set
Term Γ Ω U = Exp Γ (Left (inj₂ Ω) U)

Spine : (Γ : Ctx) (L- : List (Type ⁻)) (L+ : List (Type ⁺)) (U : Conc) → Set
Spine Γ L- L+ U = Exp Γ (Left (inj₁ (L- , L+)) U)

-- Loading mode for the left multifocused 
data Exp-l (Γ : Ctx) : SeqForm → Set

Spine-l : (Γ : Ctx) (L- : List (Type ⁻)) (U : Conc) → Set
Spine-l Γ L- U = Exp-l Γ (Left (inj₁ (L- , [])) U)


data Exp-l Γ where

  focL-step : ∀{A L U} 
    (pf : stable U)
    (In : Pers A ∈  Γ)
    (Sp : Spine-l Γ (A ∷ L) U)
    → Spine-l Γ L U
  focL-end : ∀{L U}
    (pf : stable U)
    (Sp : Spine Γ L [] U)
    → Spine-l Γ L U

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
  focL-init : ∀{U}
    (pf : stable U)
    (Sp : Spine-l Γ [] U)
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
  id⁻ : ∀{X : Type ⁻}
    → Spine Γ [ X ] [] (Susp X)

  ↑L-cons : ∀{x L- L+ U}
    (pf : stable U)
    → (N : Spine Γ L- (L+ ++ [ x ])  U)
    → Spine Γ  (↑ x ∷ L-) L+ U 

  {- Without a not nil restriction this gives weird things -}
  ↑L-nil : ∀{X L+ U}
    (pf : stable U)
    → (N : Term Γ (X ∷ L+) U)
    → Spine Γ [] (X ∷ L+) U 
  
  ⊃L : ∀{A B L- L+ U}
    (V : Value Γ A)
    (Sp : Spine Γ (B ∷ L-) L+ U) 
    → Spine Γ (A ⊃ B ∷ L-) L+ U
  ∧⁻L₁ : ∀{A B L- L+ U}
    (Sp : Spine Γ (A ∷ L-) L+ U)
    → Spine Γ (A ∧⁻ B ∷ L-) L+ U
  ∧⁻L₂ : ∀{A B L- L+ U}
    (Sp : Spine Γ (B ∷ L-) L+ U)
    → Spine Γ (A ∧⁻ B ∷ L-) L+ U



height : ∀{Γ S} → Exp Γ S → ℕ 
height-l : ∀{Γ S} → Exp-l Γ S → ℕ 

height-l (focL-step pf In Sp) = 1 + height-l Sp
height-l (focL-end pf Sp) = 1 + height Sp

height (id⁺ v) = 1
height (↓R N) = 1 + height N
height (∨R₁ V) = 1 + height V
height (∨R₂ V) = 1 + height V
height ⊤⁺R = 1
height (∧⁺R V₁ V₂) = 1 + _⊔_ (height V₁) (height V₂)
height (focR V) = 1 + height V
height (focL-init pf Sp) = 1 + height-l Sp
height (η⁺ N) = 1 + height N
height (↓L N) = 1 + height N
height ⊥L = 1
height (∨L N₁ N₂) = 1 + _⊔_ (height N₁) (height N₂)
height (⊤⁺L N) = 1 + height N
height (∧⁺L N) = 1 + height N
height (η⁻ N) = 1 + height N
height (↑R N) = 1 + height N
height (⊃R N) = 1 + height N
height ⊤⁻R = 1
height (∧⁻R N₁ N₂) = 1 + _⊔_ (height N₁) (height N₂)
height id⁻ = 1
height (↑L-cons pf N) = 1 + height N
height (↑L-nil pf N) = 1 + height N
height (⊃L V Sp) = 1 + _⊔_  (height V) (height Sp)
height (∧⁻L₁ Sp) = 1 + height Sp
height (∧⁻L₂ Sp) = 1 + height Sp



postulate 
  height-neq-zero : ∀{Γ S} → ∀{E} → height {Γ} {S} E >′ zero

postulate 
  heightl-neq-zero : ∀{Γ S} → ∀{E} → height-l {Γ} {S} E >′ zero

zero-eq-gt-absurd : ∀{x} → x ≡ zero → x >′ zero → ⊥
zero-eq-gt-absurd {zero} Eq ()
zero-eq-gt-absurd {suc x'} () (>′-refl m≡n)
zero-eq-gt-absurd {suc x'} () (>′-step Ineq)


zero-height-absurd : ∀{Γ S e} → height {Γ} {S} e ≡ zero → ⊥ 
zero-height-absurd {e = e} Eq = zero-eq-gt-absurd Eq  (height-neq-zero {E  = e})





end-inv : ∀{Γ X Y U} 
  → stable U
  → (L : List (Type ⁻)) 
  → Exp Γ (Left (inj₁ (X ∷ Y ∷ L , [])) U) 
  → ↑ ⊥⁺ ∈ L ⊎ 
      (∃ λ L+ → Exp Γ (Left (inj₁ ([] , L+)) U)) 
end-inv pf L Exp with (in-or-not L (↑ ⊥⁺))
end-inv pf L Exp | inj₁ x = inj₁ x
end-inv pf L (↑L-cons pf1 N) | inj₂ y = inj₂ (⊥⁺ ∷ [] , ↑L-nil pf ⊥L)
end-inv pf L (⊃L V Sp) | inj₂ y = inj₂ (⊥⁺ ∷ [] , ↑L-nil pf ⊥L)
end-inv pf L (∧⁻L₁ Sp) | inj₂ y = inj₂ (⊥⁺ ∷ [] , ↑L-nil pf ⊥L)
end-inv pf L (∧⁻L₂ Sp) | inj₂ y = inj₂ (⊥⁺ ∷ [] , ↑L-nil pf ⊥L)



postulate exch-cons : ∀{Γ Γ' LA C x} → Term (x ∷ Γ ++ Γ') LA C → Term (Γ ++ x ∷ Γ') LA C



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


simp-any-pers-susp : ∀{Γ x A L} 
  → (Γ' : Ctx)
  → Any (_≡_ x) (Data.List.map Pers L)
  → Any (_≡_ x) (Γ' ++ HSusp A ∷ Γ)
  → Any (_≡_ x) (Γ' ++ Γ)
simp-any-pers-susp {L = L} [] X (here refl) = ⊥-elim (no-hsusp-in-pers L X)
simp-any-pers-susp [] X (there Y) = Y
simp-any-pers-susp (x₁ ∷ Γ') X (here refl) = here refl
simp-any-pers-susp (x₁ ∷ Γ') X (there Y) = there (simp-any-pers-susp Γ' X Y)

postulate 
  pers-hsusp-subset : 
    ∀{L' Γ Γ' A} 
    → (Data.List.map Pers L') ⊆ (Γ' ++ HSusp A ∷ Γ) 
    → Data.List.map Pers L' ⊆ Γ' ++ Γ






fuse-gen : List ((List (Type ⁻) × List (Type ⁺)) ⊎ List (Type ⁺))
  → List (Type ⁺) → List (Type ⁻) × List (Type ⁺) 
fuse-gen [] LL+ = ([] , LL+)
fuse-gen (inj₁ (L- , L+) ∷ L) LL+ = L- ++ proj₁ (fuse-gen L LL+) , L+ ++ proj₂ (fuse-gen L LL+)
fuse-gen (inj₂ L+ ∷ L) LL+ = proj₁ (fuse-gen L LL+) , L+ ++ proj₂ (fuse-gen L LL+)


fuse-gen-expand : ∀{LL L+} → fuse-gen LL L+ ≡ proj₁ (fuse-gen LL L+) , proj₂ (fuse-gen LL L+)
fuse-gen-expand = refl

fuse-gen-proj₁ : ∀{LL L+ L'+} →  proj₁ (fuse-gen LL (L+ ++ L'+)) ≡ proj₁ (fuse-gen LL L+)
fuse-gen-proj₁ {[]} = λ {L+} {L'+} → refl
fuse-gen-proj₁ {inj₁ x ∷ LL} {L+} {L'+} with fuse-gen-proj₁ {LL = LL} {L+ = L+} {L'+ = L'+}
... | Eq rewrite Eq = refl
fuse-gen-proj₁ {inj₂ y ∷ LL} = fuse-gen-proj₁ {LL = LL}


fuse-gen-proj₂  : ∀{LL L+ RA} 
  → proj₂ (fuse-gen LL (L+ ++ RA)) ≡ 
    proj₂ (fuse-gen LL L+) ++ RA 
fuse-gen-proj₂ {LL = []} = refl
fuse-gen-proj₂ {LL = inj₁ x ∷ LL} {L+} {RA} with fuse-gen-proj₂ {LL} {L+} {RA}
... | Eq rewrite Eq | assoc (proj₂ x)  (proj₂ (fuse-gen LL L+)) (RA) = refl
fuse-gen-proj₂ {LL = inj₂ y ∷ LL} {L+} {RA} with fuse-gen-proj₂ {LL} {L+} {RA}
... | Eq rewrite Eq  | assoc y  (proj₂ (fuse-gen LL L+)) (RA) = refl









