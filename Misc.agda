open import Relation.Binary.PropositionalEquality 
open import Data.List
open import Reflection renaming (Term to RTerm)


postulate
  trustme : ∀ {a} {A : Set a} {x y : A} → x ≡ y

admit : RTerm → RTerm
admit _ = def (quote trustme) []
