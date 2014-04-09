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
  Left : (List (Type ⁻) × List (Type ⁺)) → (U : Conc) → SeqForm 

suspnormalF : SeqForm → Set
suspnormalF (Rfoc A) = ⊤
suspnormalF (Left L U) = suspnormal U

data Exp (Γ : Ctx) : SeqForm → Set


Value : (Γ : Ctx) → Type ⁺ → Set
Value Γ A = Exp Γ (Rfoc A)
  
Term : (Γ : Ctx) → List (Type ⁺) → Conc → Set
Term Γ Ω U = Exp Γ (Left ([] , Ω) U)

Spine : (Γ : Ctx) (L- : List (Type ⁻)) (L+ : List (Type ⁺)) (U : Conc) → Set
Spine Γ L- L+ U = Exp Γ (Left (L- , L+) U)

-- Loading mode for the left multifocused 
data Exp-l (Γ : Ctx) : SeqForm → Set

Spine-l : (Γ : Ctx) (L- : List (Type ⁻)) (U : Conc) → Set
Spine-l Γ L- U = Exp-l Γ (Left (L- , []) U)


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
    → (N : Spine Γ L-  (x ∷ L+) U)
    → Spine Γ  (↑ x ∷ L-) L+ U 

  ↑L-nil : ∀{L+ U}
    (pf : stable U)
    → (N : Term Γ L+ U)
    → Spine Γ [] L+ U 
  
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
height (⊃L V Sp) = 1 + height Sp
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
  → All (λ A → Exp (Γ' ++ Γ) (Left ([] , Ω) (Inv A))) xs
  → All (λ A → Exp (B ∷ (Γ' ++ Γ)) (Left ([] , Ω) (Inv A))) xs
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


postulate 
  in-or-not : ∀{b} {B : Set b} (L : List B) (X : B) → X ∈ L ⊎ X ∉ L

end-inv : ∀{Γ X Y U} 
  → (L : List (Type ⁻)) 
  → Exp Γ (Left (X ∷ Y ∷ L , []) U) 
  → ↑ ⊥⁺ ∈ L ⊎ 
      (∃ λ L+ → Exp Γ (Left ([] , L+) U)) 
end-inv L Exp with (in-or-not L (↑ ⊥⁺))
end-inv L Exp | inj₁ x = inj₁ x
end-inv L (↑L-cons pf N) | inj₂ y = inj₂ (⊥⁺ ∷ [] , ⊥L)
end-inv L (⊃L V Sp) | inj₂ y = inj₂ (⊥⁺ ∷ [] , ⊥L)
end-inv L (∧⁻L₁ Sp) | inj₂ y = inj₂ (⊥⁺ ∷ [] , ⊥L)
end-inv L (∧⁻L₂ Sp) | inj₂ y = inj₂ (⊥⁺ ∷ [] , ⊥L)



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
  cons-nil-cons-concat : ∀{b} {B : Set b} {x : B} {C : List B} {A : B} {L : List B} 
    → _≡_ {A = List B} (x ∷ C ++ A ∷ L) (x ∷ (C ++ A ∷ []) ++ L)

postulate 
  in-sing-sub : ∀{b} {B : Set b} {L : List B} {A : B} → (A ∈ L) → (A ∷ []) ⊆ L

postulate
  sub-in-append : ∀{Γ X A C} → X ∷ Data.List.map Pers C ⊆ Γ → Pers A ∈ Γ → X ∷ Data.List.map Pers (C ++ A ∷ []) ⊆ Γ


postulate 
  subseteq-cplx :  ∀{L Γ' Γ A} → Data.List.map Pers L ⊆ Γ' ++ Pers A ∷ Γ
                 → A ∈ L
                 → ∃ λ L1 
                 → ∃ λ L2
                 → (L ≡ (L1 ++ A ∷ L2)) -- × ((L1 ⊆ (Γ' ++ Γ)) × (L2 ⊆ Γ' ++ Γ))



loading-done : ∀{Γ L U}
  → (s : Spine-l Γ L U)
  → ∃ λ L' →  (Data.List.map Pers L') ⊆ Γ ×
    Σ (Spine Γ (L' ++ L) [] U)  (\s' → height-l s >′ height s')


loading-done {L = L} (focL-step {A = A} pf In Sp)  with loading-done Sp 
loading-done {L = L} (focL-step {A = A} pf In Sp) | [] , Sub , Sp' , IEq = 
  (A ∷ []) , (in-sing-sub In , (Sp' , >′-step IEq))
loading-done {L = L} (focL-step {A = A} pf In Sp) | x ∷ C , Sub , Sp' , IEq 
  rewrite cons-nil-cons-concat {x = x} {C = C} {A = A} {L = L}  = 
     x ∷ C ++ A ∷ [] , (sub-in-append Sub In , (Sp' , >′-step IEq))
loading-done {Γ} (focL-end pf Sp) = [] , (λ {x} → λ ()) ,  Sp , >′-refl refl 

unload-all-l : ∀{Γ U} → (L : List (Type ⁻)) → (pf : stable U) → Spine-l Γ L U → Data.List.map Pers L ⊆ Γ → Spine-l Γ [] U 
unload-all-l [] pf Sp In = Sp
unload-all-l (x ∷ L) pf Sp In = unload-all-l L pf (focL-step pf (In (here refl)) Sp) (λ {x₁} z → In (there z))


unload-all : ∀{Γ U} → (L : List (Type ⁻)) → (pf : stable U) → Spine Γ L [] U → Data.List.map Pers L ⊆ Γ → Spine Γ [] [] U 
unload-all [] pf Sp In = Sp
unload-all (x ∷ L) pf Sp In = focL-init pf (unload-all-l (x ∷ L)  pf (focL-end pf Sp) In)


subst⁺-l : ∀{Γ A Form} (Γ' : Ctx)
  → Value (Γ' ++ Γ) A
  → Exp-l (Γ' ++ HSusp A ∷ Γ) Form
  → Exp-l (Γ' ++ Γ) Form

subst⁺ : ∀{Γ A Form} (Γ' : Ctx)
  → Value (Γ' ++ Γ) A
  → Exp (Γ' ++ HSusp A ∷ Γ) Form
  → Exp (Γ' ++ Γ) Form

subst⁺-l Γ' V (focL-step pf In Sp) with fromctx Γ' In
... |  inj₁ ()
... |  inj₂ y = focL-step pf y (subst⁺-l Γ' V Sp) 
subst⁺-l Γ' V (focL-end pf Sp) = focL-end pf (subst⁺ Γ' V Sp) 

subst⁺ Γ' V (id⁺ x) with fromctx Γ' x
subst⁺ Γ' V (id⁺ x) | inj₁ refl = V
subst⁺ Γ' V (id⁺ x) | inj₂ y = id⁺ y
subst⁺ Γ' V (↓R N) = ↓R (subst⁺ Γ' V N)
subst⁺ Γ' V (∨R₁ V') = ∨R₁ (subst⁺ Γ' V V')
subst⁺ Γ' V (∨R₂ V') = ∨R₂ (subst⁺ Γ' V V')
subst⁺ Γ' V ⊤⁺R = ⊤⁺R
subst⁺ Γ' V (∧⁺R V₁ V₂) = ∧⁺R (subst⁺ Γ' V V₁) (subst⁺ Γ' V V₂)

subst⁺ Γ' V (focR V') = focR (subst⁺ Γ' V V')
subst⁺ Γ' V (focL-init pf Sp)   with loading-done Sp
... | L'  , Sub , Exp , Ieq = {!unload-all 
    L' 
    ?
    (subst⁺ ?
                 Exp 
                 ?
                 --(subst (\x → x  >′ height Exp) (sym H) (>′-step Ieq))

    ) 
    Sub !}
  --focL-init pf (subst⁺-l Γ' V Sp) 
    
subst⁺ Γ' V (η⁺ N) = η⁺ (subst⁺ (_ ∷ Γ') (wken V) N)
subst⁺ Γ' V (η⁻ N) = η⁻ (subst⁺ Γ' V N)
subst⁺ Γ' V (↓L N) = ↓L (subst⁺ (_ ∷ Γ') (wken V) N)
subst⁺ Γ' V (↑R N) = ↑R (subst⁺ Γ' V N)
subst⁺ Γ' V ⊥L = ⊥L
subst⁺ Γ' V (∨L N₁ N₂) = ∨L (subst⁺ Γ' V N₁) (subst⁺ Γ' V N₂)
subst⁺ Γ' V (⊤⁺L N) = ⊤⁺L (subst⁺ Γ' V N)
subst⁺ Γ' V (∧⁺L N) = ∧⁺L (subst⁺ Γ' V N)
subst⁺ Γ' V (⊃R N) = ⊃R (subst⁺ Γ' V N)
subst⁺ Γ' V ⊤⁻R = ⊤⁻R
subst⁺ Γ' V (∧⁻R N₁ N₂) = ∧⁻R (subst⁺ Γ' V N₁) (subst⁺ Γ' V N₂)

subst⁺ Γ' V id⁻ = id⁻
subst⁺ Γ' V (↑L-nil pf N) = ↑L-nil pf (subst⁺ Γ' V N)
subst⁺ Γ' V (↑L-cons pf N) = ↑L-cons pf (subst⁺ Γ' V N) 
subst⁺ Γ' V (⊃L V' Sp) = ⊃L (subst⁺ Γ' V V') (subst⁺ Γ' V Sp)
subst⁺ Γ' V (∧⁻L₁ Sp) = ∧⁻L₁ (subst⁺ Γ' V Sp)
subst⁺ Γ' V (∧⁻L₂ Sp) = ∧⁻L₂ (subst⁺ Γ' V Sp)


postulate 
  subseteq-cons : ∀{b} {B : Set b} {L : List B}  {X M} → L ⊆ M → X ∈ M → (X ∷ L) ⊆ M

subseteq-drop-cons : ∀{b} {B : Set b} {X : B} {Y L} → (X ∷ Y) ⊆ L → Y ⊆ L
subseteq-drop-cons = λ x x₂ → x (there x₂)



cons-equiv : ∀{b} {B : Set b} {x : B} (L L' : List B) → (L ≡ L') → _≡_ {A = List B} (x ∷ L) (x ∷ L')
cons-equiv L .L refl = refl

concat-nil : ∀{b} {B : Set b} (L : List B) → (L ++ []) ≡ L
concat-nil [] = refl
concat-nil (x ∷ L) = cons-equiv (L ++ []) L (concat-nil L)



subst⁻-help : ∀{Γ A L U z}
  → stable U
  → (e : Exp Γ (Left L (Susp A)))
  → (z >′ height e)
  → Spine Γ [ A ] [] U
  → Exp Γ (Left L U)

subst⁻ : ∀{Γ A L U z}
  → stable U
  → (e : Exp Γ (Left L (Susp A)))
  → (z ≡ height e)
  → Spine Γ [ A ] [] U
  → Exp Γ (Left L U)

subst⁻-help {L = proj₁ , proj₂} pf Exp (>′-refl m≡n) Sp = subst⁻ pf Exp m≡n Sp
subst⁻-help {L = proj₁ , proj₂} pf Exp (>′-step Ineq) Sp = subst⁻-help pf Exp Ineq Sp





subst⁻  {z = zero} pf _ H Sp' = ⊥-elim (zero-height-absurd (sym H))
subst⁻  {Γ} {A} {z = z} pf (focL-init pf' Sp) H Sp' with loading-done Sp
... | L'  , Sub , Exp , Ieq rewrite concat-nil L'  = unload-all 
    L' 
    pf 
    (subst⁻-help {z = z} 
                 pf 
                 Exp 
                 (subst (\x → x  >′ height Exp) (sym H) (>′-step Ieq))
                 Sp'
    ) 
    Sub 
subst⁻ {L = .[] , ._} {z = suc z'} pf (↓L N) H Sp = ↓L (subst⁻ pf N ((suc-inj H)) (wken Sp))
subst⁻ {z = suc z'} pf (η⁺ N) H Sp = η⁺ (subst⁻ pf N (suc-inj H) (wken Sp))
subst⁻ {L = .[] , ._} {z = suc z'} pf ⊥L H Sp = ⊥L
subst⁻ {L = .[] , ._} {z = suc z'} pf (∨L N₁ N₂) H Sp = 
  ∨L 
    (subst⁻-help {z = suc z'} pf N₁ (suc-max-left H) Sp) 
    (subst⁻-help {z = suc z'} pf N₂ (suc-max-right {x = height N₁} H) Sp)  
subst⁻ {L = .[] , ._} {z = suc z'} pf (⊤⁺L N) H Sp = ⊤⁺L (subst⁻ pf N (suc-inj H) Sp)
subst⁻ {L = .[] , ._} {z = suc z'} pf (∧⁺L N) H Sp = ∧⁺L (subst⁻ pf N (suc-inj H) Sp)
subst⁻ {L = ._ , .[]} {z = suc z'} pf id⁻ H Sp = Sp
subst⁻ {L = ._ , proj₂} {z = suc z'} pf (↑L-cons pf₁ N) H Sp = ↑L-cons pf (subst⁻ pf N (suc-inj H) Sp) 
subst⁻ {L = .[] , proj₂} {z = suc z'} pf (↑L-nil pf₁ N) H Sp = ↑L-nil pf (subst⁻ pf N (suc-inj H) Sp)
subst⁻ {L = ._ , proj₂} {z = suc z'} pf (⊃L V Sp) H Sp' = ⊃L V (subst⁻ pf Sp (suc-inj H) Sp')
subst⁻ {L = ._ , proj₂} {z = suc z'} pf (∧⁻L₁ Sp) H Sp' =  ∧⁻L₁ (subst⁻ pf Sp (suc-inj H) Sp') 
subst⁻  {L = ._ , proj₂} {z = suc z'} pf (∧⁻L₂ Sp) H Sp' = ∧⁻L₂ (subst⁻ pf Sp (suc-inj H) Sp') 







subst-' : ∀{Γ A L- L+ L+' U}
  → stable U
  → Spine Γ L- L+ (Susp A)
  → Spine Γ [ A ] L+' U
  → Spine Γ L- (L+ ++ L+') U


subst-' {L+ = L+} pf Sp1 id⁻ rewrite concat-nil L+ = Sp1
subst-' pf Sp1 (↑L-cons pf₁ N) = {!!}
subst-' pf Sp1 (⊃L V Sp) = {!!}
subst-' pf Sp1 (∧⁻L₁ Sp) = {!!}
subst-' pf Sp1 (∧⁻L₂ Sp) = {!!}



