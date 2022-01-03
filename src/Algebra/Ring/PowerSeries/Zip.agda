{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
-- | Zip products; i.e. componentwise products.
module Algebra.Ring.PowerSeries.Zip {ℓ} (R : CommRing ℓ) where
open import Cubical.Algebra.Ring
open import Algebra.Ring.PowerSeries.Base R
open import Algebra.Ring.PowerSeries.Addition R
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.RingSolver.ReflectionSolving
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.Ring.Properties
open import Algebra.Ring.PowerSeries.Module R
open import Cubical.Data.Nat
  using ( ℕ ; suc )
  renaming (_+_ to _+ℕ_; _·_ to _·ℕ_)
open import Lemmas.IsoEquiv
open PowerSeries

open CommRingStr (snd R) renaming 
  ( _·_ to _·R_ ; _+_ to _+R_; 1r to 1R; 0r to 0R
  ; _-_ to _-R_; -_ to -R_
  ; +Assoc to +R-assoc
  ; +Identity to +R-identity
  ; +Comm to +R-comm
  ; ·Assoc to ·R-assoc
  ; ·-comm to ·R-comm
  ; ·Identity to ·R-identity
  ; is-set to R-isSet
  ; ·Rdist+ to R-·Rdist+
  ; ·Ldist+ to R-·Ldist+
  )

infixl 8 _⊗_
_⊗_ : PowerSeries → PowerSeries → PowerSeries
head (f ⊗ g) = head f ·R head g
tail (f ⊗ g) = tail f ⊗ tail g

repeat : ⟨ R ⟩ → PowerSeries
head (repeat x) = x
tail (repeat x) = repeat x

1rep : PowerSeries
1rep = repeat 1R

⊗-identity-l : ∀ x → 1rep ⊗ x ≡ x
head (⊗-identity-l x i) = snd (·R-identity (head x)) i
tail (⊗-identity-l x i) = ⊗-identity-l (tail x) i

⊗-identity-r : ∀ x → x ⊗ 1rep ≡ x
head (⊗-identity-r x i) = fst (·R-identity (head x)) i
tail (⊗-identity-r x i) = ⊗-identity-r (tail x) i

⊗-assoc : ∀ x y z → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z
head (⊗-assoc f g h i) = ·R-assoc (head f) (head g) (head h) i
tail (⊗-assoc f g h i) = ⊗-assoc (tail f) (tail g) (tail h) i

⊗-isSemigroup : IsSemigroup _⊗_
⊗-isSemigroup = issemigroup PowerSeries-isSet ⊗-assoc

⊗-isMonoid : IsMonoid 1rep _⊗_
⊗-isMonoid = ismonoid ⊗-isSemigroup (λ x → (⊗-identity-r x , ⊗-identity-l x))

⊗Ldist+ : ∀ f g h → (f + g) ⊗ h ≡ (f ⊗ h) + (g ⊗ h)
head (⊗Ldist+ f g h i) = R-·Ldist+ (head f) (head g) (head h) i
tail (⊗Ldist+ f g h i) = ⊗Ldist+ (tail f) (tail g) (tail h) i

⊗Rdist+ : ∀ f g h → f ⊗ (g + h) ≡ (f ⊗ g) + (f ⊗ h)
head (⊗Rdist+ f g h i) = R-·Rdist+ (head f) (head g) (head h) i
tail (⊗Rdist+ f g h i) = ⊗Rdist+ (tail f) (tail g) (tail h) i

⊗-IsRing : IsRing 0s 1rep _+_ _⊗_ -_
⊗-IsRing = isring +-isAbGroup ⊗-isMonoid (λ f g h → ⊗Rdist+ f g h , ⊗Ldist+ f g h)

⊗-comm : ∀ f g → f ⊗ g ≡ g ⊗ f
head (⊗-comm f g i) = ·R-comm (head f) (head g) i
tail (⊗-comm f g i) = ⊗-comm (tail f) (tail g) i

⊗-IsCommRing : IsCommRing 0s 1rep _+_ _⊗_ -_
⊗-IsCommRing = iscommring ⊗-IsRing ⊗-comm

⊗-CommRingStr : CommRingStr PowerSeries
⊗-CommRingStr = commringstr 0s 1rep _+_ _⊗_ -_ ⊗-IsCommRing

⊗-CommRing : CommRing _
⊗-CommRing = (_ , ⊗-CommRingStr)
