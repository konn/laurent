{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.Ring.PowerSeries.Addition {ℓ} (R : CommRing ℓ) where
open import Algebra.Ring.PowerSeries.Base R
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Data.Nat
  using ( ℕ ; suc )
  renaming (_+_ to _+ℕ_; _·_ to _·ℕ_)

open PowerSeries

open CommRingStr (snd R) renaming 
  ( _·_ to _·R_ ; _+_ to _+R_; -_ to -R_; 1r to 1R; 0r to 0R
  ; _-_ to _-R_
  ; +Assoc to +R-assoc
  ; +Comm to +R-comm
  ; +Identity to +R-identity
  ; +Inv to +R-inverse
  ; ·Assoc to ·R-assoc
  ; ·Identity to ·R-identity
  ; is-set to R-isSet
  )

infixl 7 _+_
_+_ : PowerSeries → PowerSeries → PowerSeries
head (l + r) = head l +R head r
tail (l + r) = tail l + tail r

infixl 7 _+ℕ→_
_+ℕ→_ : (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩)
_+ℕ→_ = liftSeriesOp₂ _+_

+ℕ→-compwise-n : ∀ f g n → (f +ℕ→ g) n ≡ f n +R g n
+ℕ→-compwise-n f g 0 =  
    (f +ℕ→ g) 0
  ≡[ i ]⟨ liftSeriesOp₂-unfold _+_ f g i 0 ⟩
    Series⟶ℕ→R (ℕ→R⟶Series f + ℕ→R⟶Series g) 0
  ≡⟨ refl ⟩
    f 0 +R g 0
  ∎
+ℕ→-compwise-n f g (suc n) = +ℕ→-compwise-n (λ n → f (suc n)) (λ n → g (suc n)) n

+ℕ→-compwise : ∀ f g → (f +ℕ→ g) ≡ (λ n → f n +R g n)
+ℕ→-compwise f g i n = +ℕ→-compwise-n f g n i

+-assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
head (+-assoc x y z i) = +R-assoc (head x) (head y) (head z) i
tail (+-assoc x y z i) = +-assoc (tail x) (tail y) (tail z) i

+-identityʳ : ∀ x  → x + 0s ≡ x
head (+-identityʳ x i) = fst (+R-identity (head x)) i
tail (+-identityʳ x i) = +-identityʳ (tail x) i

+-identityˡ : ∀ x  → 0s + x ≡ x
head (+-identityˡ x i) = snd (+R-identity (head x)) i
tail (+-identityˡ x i) = +-identityˡ (tail x) i

+-identity : ∀ x → (x + 0s ≡ x) × (0s + x ≡ x)
+-identity x = (+-identityʳ x , +-identityˡ x)

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = issemigroup PowerSeries-isSet +-assoc

+-isMonoid : IsMonoid 0s _+_
+-isMonoid = ismonoid +-isSemigroup +-identity

infix  8 -_

-_ : PowerSeries → PowerSeries
head (- f) = -R (head f)
tail (- f) = - (tail f)

+-inverseˡ : ∀ x → (- x) + x ≡ 0s
head (+-inverseˡ x i) = snd (+R-inverse (head x)) i
tail (+-inverseˡ x i) = +-inverseˡ (tail x) i

+-inverseʳ : ∀ x → x + (- x) ≡ 0s
head (+-inverseʳ x i) = fst (+R-inverse (head x)) i
tail (+-inverseʳ x i) = +-inverseʳ (tail x) i

+-inverse : ∀  x → (x + (- x) ≡ 0s) × ((- x) + x ≡ 0s)
+-inverse x = (+-inverseʳ x , +-inverseˡ x)

+-isGroup : IsGroup 0s _+_ -_
+-isGroup =
  isgroup +-isMonoid +-inverse

+-comm : ∀ f g → f + g ≡ g + f
head (+-comm f g i) = +R-comm (head f) (head g) i
tail (+-comm f g i) = +-comm (tail f) (tail g) i

+-isAbGroup : IsAbGroup 0s _+_ -_
+-isAbGroup = isabgroup +-isGroup +-comm
 