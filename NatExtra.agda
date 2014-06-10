open import Data.Nat  hiding (_≤′_; module _≤′_; _<′_; _≥′_; _>′_)
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])

module NatExtra where



assoc-nat : ∀{X Y Z} → X + (Y + Z) ≡ X + Y + Z 
assoc-nat {zero} = λ {Y} {Z} → refl
assoc-nat {suc X} {Y} {Z} rewrite assoc-nat {X} {Y} {Z} = refl  

suc-inj : ∀{x x' : ℕ} → suc x ≡ suc x' → x ≡ x'
suc-inj refl = refl

suc-≡ : ∀{x x' : ℕ} → x ≡ x' → suc x ≡ suc x'
suc-≡ refl = refl 



infix 4 _>′_

data _>′_ : (m : ℕ) → ℕ → Set where
  >′-refl : ∀ {m n} (m≡n : m ≡ n) → suc m >′ n
  >′-step : ∀ {m n} (m≤′n : m >′ n) → suc m >′ n


suc->′-suc : ∀{m n} → m >′ n → suc m >′ suc n
suc->′-suc (>′-refl refl) = >′-refl refl
suc->′-suc (>′-step Ineq) =  >′-step (suc->′-suc Ineq)

suc-+-refl->′ : ∀{m} → (N : ℕ) → suc (N + m)  >′ m
suc-+-refl->′ {m} zero = >′-refl refl 
suc-+-refl->′ {m} (suc N) = >′-step (suc-+-refl->′ N)


+-n-n->′ : ∀{n m k} → k >′ m → n + k >′ n + m
+-n-n->′ {zero} Ieq = Ieq
+-n-n->′ {suc n} {m} {k} Ieq = suc->′-suc (+-n-n->′ {n} {m} {k} Ieq) 

+-n->′ : ∀{n m k} → k >′ m → n + k >′ m
+-n->′ {zero} Ieq = Ieq
+-n->′ {suc n} {m} {k} Ieq = >′-step (+-n->′ {n = n} Ieq) 

+-suc->′ : ∀{m n} → suc m + n >′ n
+-suc->′ {zero} = λ {n} → >′-refl refl
+-suc->′ {suc m} {n} = >′-step (+-suc->′ {m = m})

suc-gt-zero : (b : ℕ) → suc b >′ zero
suc-gt-zero zero = >′-refl refl
suc-gt-zero (suc b) = >′-step (suc-gt-zero b)



-- ABOUT MAX
max-left : ∀{x y z} → z ≡ (x ⊔ y) →  suc z >′ x
max-left {zero} {zero} refl = >′-refl refl
max-left {suc x} {zero} refl = >′-refl refl
max-left {zero} {suc y} refl = suc-gt-zero (suc y)
max-left {suc x} {suc y} {zero} ()
max-left {suc x} {suc y} {suc z} Eq = suc->′-suc (max-left (suc-inj Eq))

suc-max-left  : ∀{x y z} → suc z ≡ suc (x ⊔ y) →  suc z >′ x
suc-max-left {x} {y} {z} Eq = max-left (suc-inj Eq)

max-right : ∀{x y z} → z ≡ (x ⊔ y) →  suc z >′ y
max-right {zero} {zero} Eq = >′-refl Eq
max-right {zero} {suc y} Eq = >′-refl Eq
max-right {suc x} {zero} {z} Eq = suc-gt-zero z
max-right {suc x} {suc y} {zero} ()
max-right {suc x} {suc y} {suc z} Eq = suc->′-suc (max-right {x = x} (suc-inj Eq))

suc-max-right  : ∀{x y z} → suc z ≡ suc (x ⊔ y) →  suc z >′ y
suc-max-right {x} {y} {z} Eq = max-right {x = x} (suc-inj Eq)
