open import Data.List
open import Data.List.Any
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


length-cons-nil : ∀{b c} {B : Set b} {C : Set c} {X : B} {Y : C} {L} → length (X ∷ L) ≡ length (Y ∷ []) → L ≡ []
length-cons-nil {L = []} Eq = refl
length-cons-nil {L = x ∷ L} ()

postulate
  assoc :  ∀{b} {B : Set b} (L1 L2 L3 : List B) → L1 ++ L2 ++ L3 ≡ (L1 ++ L2) ++ L3