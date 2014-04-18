open import Data.List
open import Data.List.Any
open Membership-≡
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])


module Subset where

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


postulate 
  subseteq-cons : ∀{b} {B : Set b} {L : List B}  {X M} → L ⊆ M → X ∈ M → (X ∷ L) ⊆ M

subseteq-drop-cons : ∀{b} {B : Set b} {X : B} {Y L} → (X ∷ Y) ⊆ L → Y ⊆ L
subseteq-drop-cons = λ x x₂ → x (there x₂)


postulate 
  in-sing-sub : ∀{b} {B : Set b} {L : List B} {A : B} → (A ∈ L) → (A ∷ []) ⊆ L


postulate
  sub-in-append : 
                ∀{a} {A : Set a} {L Γ : List A} {Y f} 
                → Data.List.map f L ⊆ Γ 
                → f Y ∈ Γ 
                → Data.List.map f (L ++ Y ∷ []) ⊆ Γ


postulate 
  cons-sub-in-append : 
                     ∀{a} {A : Set a} {L : List A} 
                     {b} {B : Set b} {Γ : List B} {X Y f} 
                     → X ∷ Data.List.map f L ⊆ Γ 
                     → f Y ∈ Γ 
                     → X ∷ Data.List.map f (L ++ Y ∷ []) ⊆ Γ



postulate 
  subseteq-cplx : ∀{a} {A : Set a} {L Γ' : List A} {Γ f X} 
    → Data.List.map f L ⊆ Γ' ++ f X ∷ Γ
    → X ∈ L
    → ∃ λ L1 
    → ∃ λ L2
    → (L ≡ (L1 ++ X ∷ L2)) -- × ((L1 ⊆ (Γ' ++ Γ)) × (L2 ⊆ Γ' ++ Γ))
