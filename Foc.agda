
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
open import Data.List.Any.Properties
open import Data.List.All
-- open import Function.Related
open import Function.Inverse hiding (sym)
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
    (pf : stable U)
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
wk θ (↑L pf N) = ↑L pf (wk θ N)
wk θ (⊃L V Sp) = ⊃L (wk θ V) (wk θ Sp)
wk θ (∧⁻L₁ Sp) = ∧⁻L₁ (wk θ Sp)
wk θ (∧⁻L₂ Sp) = ∧⁻L₂ (wk θ Sp)


wken : ∀{Γ A Form} → Exp Γ Form → Exp (A ∷ Γ) Form
wken = wk (λ {x} → there)

wk-middle : ∀{Γ Form} → (Γ' : Ctx) → (L : Ctx) → Exp (Γ' ++ Γ) Form → Exp (Γ' ++ L ++ Γ) Form
wk-middle [] [] Exp = Exp
wk-middle [] (x ∷ L) Exp = wken (wk (\z → ++ʳ L z) Exp)
wk-middle (x ∷ Γ') L Exp = {!!} 

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




subst⁺ : ∀{Γ A Form} (Γ' : Ctx)
  → Value (Γ' ++ Γ) A
  → Exp (Γ' ++ HSusp A ∷ Γ) Form
  → Exp (Γ' ++ Γ) Form

subst⁺ Γ' V (id⁺ x) with fromctx Γ' x
subst⁺ Γ' V (id⁺ x) | inj₁ refl = V
subst⁺ Γ' V (id⁺ x) | inj₂ y = id⁺ y
subst⁺ Γ' V (↓R N) = ↓R (subst⁺ Γ' V N)
subst⁺ Γ' V (∨R₁ V') = ∨R₁ (subst⁺ Γ' V V')
subst⁺ Γ' V (∨R₂ V') = ∨R₂ (subst⁺ Γ' V V')
subst⁺ Γ' V ⊤⁺R = ⊤⁺R
subst⁺ Γ' V (∧⁺R V₁ V₂) = ∧⁺R (subst⁺ Γ' V V₁) (subst⁺ Γ' V V₂)

subst⁺ Γ' V (focR V') = focR (subst⁺ Γ' V V')
subst⁺ Γ' V (focL pf x Sp) with fromctx Γ' x
... | inj₁ ()
... | inj₂ y = focL pf y (subst⁺ Γ' V Sp)
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
subst⁺ Γ' V (↑L pf N) = ↑L pf (subst⁺ Γ' V N)
subst⁺ Γ' V (⊃L V' Sp) = ⊃L (subst⁺ Γ' V V') (subst⁺ Γ' V Sp)
subst⁺ Γ' V (∧⁻L₁ Sp) = ∧⁻L₁ (subst⁺ Γ' V Sp)
subst⁺ Γ' V (∧⁻L₂ Sp) = ∧⁻L₂ (subst⁺ Γ' V Sp)





gsubst⁺ :
  ∀{Γ Form}
  → (Γ' : Ctx)  
  → (LAi : List (Type ⁺))
  → All (\x → Value (Γ' ++ Γ) x) LAi
  → Exp (Γ' ++ Data.List.map (\x → HSusp x) (LAi) ++ Γ) Form 
  → Exp (Γ' ++ Γ) Form
  
gsubst⁺ Γ' [] PA (id⁺ v) = id⁺ v
gsubst⁺ {Γ} Γ' (x ∷ LAi) (px ∷ PA) (id⁺ {A} v)
 with  fromctxGen Γ' (Data.List.map (\x → HSusp x) (x ∷ LAi)) v
... | inj₁ (here px₁) = subst (λ z → Exp (Γ' ++ Γ) (Rfoc z)) (sym (hsusp-inj px₁)) px   
... | inj₁ (there L) = extra Γ Γ' A LAi L PA
... | inj₂ R = id⁺ R

gsubst⁺ Γ' LAi PA (↓R {A} N) = ↓R (gsubst⁺ Γ' LAi PA N)
gsubst⁺ Γ' LAi PA (∨R₁ {A} {B} V) = ∨R₁ (gsubst⁺ Γ' LAi PA V)
gsubst⁺ Γ' LAi PA (∨R₂ {A} {B} V) = ∨R₂ (gsubst⁺ Γ' LAi PA V)
gsubst⁺ Γ' LAi PA ⊤⁺R = ⊤⁺R
gsubst⁺ Γ' LAi PA (∧⁺R {A} {B} V₁ V₂) = ∧⁺R (gsubst⁺ Γ' LAi PA V₁) (gsubst⁺ Γ' LAi PA V₂)
gsubst⁺ Γ' LAi PA (focR {A} V) = focR (gsubst⁺ Γ' LAi PA V)
-- focL
gsubst⁺ Γ' LAi PA (focL {A} {U} pf x Sp) 
   with  fromctxGen Γ' (Data.List.map (\x → HSusp x) LAi) x 
gsubst⁺ Γ' [] PA (focL pf x Sp) | inj₁ L = focL pf x Sp
gsubst⁺ Γ' (x ∷ LAi) (px₁ ∷ PA) (focL pf x₁ Sp) | inj₁ (here ())
gsubst⁺ Γ' (x ∷ LAi) (px ∷ PA) (focL pf x₁ Sp) | inj₁ (there L) = ⊥-elim (no-pers-in-hsusp LAi L) 
gsubst⁺ Γ' [] PA (focL pf x Sp) | inj₂ R = focL pf R Sp
gsubst⁺ Γ' (x ∷ LAi) (px ∷ PA) (focL pf x₁ Sp) | inj₂ R = focL pf R (gsubst⁺ Γ' (x ∷ LAi) (px ∷ PA) Sp)
-- end focL
gsubst⁺ Γ' .[] [] (η⁺ N) = η⁺ N
gsubst⁺ {Γ} Γ' .(x ∷ xs) (_∷_ {x} {xs} px PA) (η⁺ {Q} N) = 
  η⁺ (gsubst⁺ (_ ∷ Γ') (x ∷ xs)  (wken-all-rfoc {Γ'} (px ∷ PA)) N )

gsubst⁺ Γ' .[] [] (↓L N) = ↓L N
gsubst⁺ {Γ} Γ' .(x ∷ xs) (_∷_ {x} {xs} px PA) (↓L {A} N) = 
  ↓L (gsubst⁺ (_ ∷ Γ') (x ∷ xs) (wken-all-rfoc {Γ'} (px ∷ PA)) N)

gsubst⁺ Γ' LAi PA (⊥L {U} {Ω}) = ⊥L
gsubst⁺ Γ' LAi PA (∨L {A} {B} {Ω} {U} N₁ N₂) = 
  ∨L (gsubst⁺ Γ' LAi PA N₁)
     (gsubst⁺ Γ' LAi PA N₂)
gsubst⁺ Γ' LAi PA (⊤⁺L {U} {Ω} N) = ⊤⁺L (gsubst⁺  Γ' LAi PA N)
gsubst⁺ Γ' LAi PA (∧⁺L {U} {Ω} {A} {B} N) = 
  ∧⁺L (gsubst⁺ Γ' LAi PA N)
gsubst⁺ Γ' LAi PA (η⁻ {Q} N) = 
  η⁻ (gsubst⁺ Γ' LAi PA N)
gsubst⁺ Γ' LAi PA (↑R {A} N) = 
  ↑R (gsubst⁺ Γ' LAi PA N)
gsubst⁺ Γ' LAi PA (⊃R {A} {B} N) = 
  ⊃R (gsubst⁺ Γ' LAi PA N)
gsubst⁺ Γ' LAi PA ⊤⁻R = ⊤⁻R
gsubst⁺ Γ' LAi PA (∧⁻R {A} {B} N₁ N₂) = 
  ∧⁻R (gsubst⁺ Γ' LAi PA N₁)
      (gsubst⁺ Γ' LAi PA N₂)
gsubst⁺ Γ' LAi PA (id⁻ {A}) = id⁻
gsubst⁺ Γ' LAi PA (↑L {A} {U} pf N) = 
  ↑L pf (gsubst⁺ Γ' LAi PA N)
gsubst⁺ Γ' LAi PA (⊃L V Sp) = ⊃L (gsubst⁺ Γ' LAi PA V) (gsubst⁺ Γ' LAi PA Sp)
gsubst⁺ Γ' LAi PA (∧⁻L₁ Sp) = ∧⁻L₁ (gsubst⁺ Γ' LAi PA Sp)
gsubst⁺ Γ' LAi PA (∧⁻L₂ Sp) = ∧⁻L₂ (gsubst⁺ Γ' LAi PA Sp)


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
subst⁻ pf (↑L _ N) Sp = ↑L pf (subst⁻ pf N Sp)
subst⁻ pf (⊃L V Sp) Sp' = ⊃L V (subst⁻ pf Sp Sp')
subst⁻ pf (∧⁻L₁ Sp) Sp' = ∧⁻L₁ (subst⁻ pf Sp Sp')
subst⁻ pf (∧⁻L₂ Sp) Sp' = ∧⁻L₂ (subst⁻ pf Sp Sp')

