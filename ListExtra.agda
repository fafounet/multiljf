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