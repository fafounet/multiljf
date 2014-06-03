open import Data.List
open import Data.Nat
open import Data.Product
open import Data.List.Any
open import Data.List.All hiding (_∷_)
open Membership-≡
open import Data.Sum
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])

module ListExtra where

cons-equiv : ∀{b} {B : Set b} {x : B} (L L' : List B) → (L ≡ L') → _≡_ {A = List B} (x ∷ L) (x ∷ L')
cons-equiv L .L refl = refl

concat-nil : ∀{b} {B : Set b} (L : List B) → (L ++ []) ≡ L
concat-nil [] = refl
concat-nil (x ∷ L) = cons-equiv (L ++ []) L (concat-nil L)

postulate 
  in-or-not : ∀{b} {B : Set b} (L : List B) (X : B) → X ∈ L ⊎ X ∉ L

postulate
  cons-nil-cons-concat : ∀{b} {B : Set b} {x : B} {C : List B} {A : B} {L : List B} 
    → _≡_ {A = List B} (x ∷ C ++ A ∷ L) (x ∷ (C ++ A ∷ []) ++ L)

length-cons-nil' : ∀{b c} {B : Set b} {C : Set c} {L : List B} 
  → suc (length (L)) ≡ suc (length {A = C} ([]))
  → L ≡ []
length-cons-nil' {L = []} Eq = refl
length-cons-nil' {L = x ∷ L} ()

length-cons-nil : ∀{b c} {B : Set b} {C : Set c} {X : B} {Y : C} {L} 
  → length (X ∷ L) ≡ length (Y ∷ []) 
  → L ≡ []
length-cons-nil {L = []} Eq = refl
length-cons-nil {L = x ∷ L} ()

postulate 
  length-cons : 
              ∀{b c} {B : Set b} {C : Set c} {X : B} {Y : C} (L : List B) (L' : List C) 
                → length (X ∷ L) ≡ length (Y ∷ L') 
                → length L ≡ length L'

postulate
  assoc :  ∀{b} {B : Set b} (L1 L2 L3 : List B) → L1 ++ L2 ++ L3 ≡ (L1 ++ L2) ++ L3

postulate
  assoc-cons-append : ∀{b} {B : Set b} (X : B) (L1 L2 L3 : List B) → X ∷ (L1 ++ L2) ++ L3 ≡ X ∷ L1 ++ L2 ++ L3

postulate
  in-append-cons : ∀{b} {B : Set b} {X : B} {L1 L2} →  X ∈ (L1 ++ X ∷ L2)

postulate
  in-append-left : ∀{b} {B : Set b} {X : B} {L1 L2} →  X ∈ L1 → X ∈ (L1 ++ L2)

postulate
  in-append-right : ∀{b} {B : Set b} {X : B} {L1 L2} →  X ∈ L2 → X ∈ (L1 ++ L2)



postulate
  in-append-weak : ∀{b} {B : Set b} {X Y : B} {L1 L2} → X ∈ (L1 ++ L2) → X ∈ (L1 ++ Y ∷ L2)


postulate
  in-append-double-weak : ∀{b} {B : Set b} {X Y Z : B} {L1 L2} → X ∈ (L1 ++ L2) → X ∈ (L1 ++ Y ∷ Z ∷ L2)

postulate
  all-append : ∀{a p} {A : Set a} {P : A → Set p} {x xs} (px : P x) (pxs : All P xs) → All P (xs ++ [ x ])


all-disjoint-sum-r : ∀{a b c} {A : Set a}  {xs : List A} {M : A → Set b} {M' : A → Set c}
  → All (λ n → M n) xs 
  → All (λ w → _⊎_ {b = c} (M w) (M' w)) xs
all-disjoint-sum-r {xs = []} A₁ = []
all-disjoint-sum-r  (px All.∷ A₁) = inj₁ px All.∷ all-disjoint-sum-r A₁

all-disjoint-sum-l : ∀{a b c} {A : Set a}  {xs : List A} {M : A → Set b} {M' : A → Set c}
  → All (λ n → M n) xs 
  → All (λ w → _⊎_ {b = b} (M' w) (M w)) xs
all-disjoint-sum-l {xs = []} A₁ = []
all-disjoint-sum-l (px All.∷ A₁) = inj₂ px All.∷ all-disjoint-sum-l A₁


in-split : ∀{a} {A : Set a} {X : A} {L : List A}  → X ∈ L → ∃ λ L1 → ∃ λ L2 → L ≡ (L1 ++ X ∷ L2)
in-split (here {xs = xs} refl) = [] , xs , refl
in-split (there In) with in-split In
in-split {X = X} (there {x} {xs} In) | L1 , L2 , Eq = x ∷ L1 , L2 , cons-equiv xs (L1 ++ X ∷ L2) Eq   