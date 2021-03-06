{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.CommRing.PowerSeries.Addition {ℓ} (R : CommRing ℓ) where
open import Algebra.CommRing.PowerSeries.Base R
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
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

infixl 7 _+'_
_+'_ : (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩)
_+'_ = liftSeriesOp₂ _+_

+'-compwise-n : ∀ f g n → (f +' g) n ≡ f n +R g n
+'-compwise-n f g 0 =  
    (f +' g) 0
  ≡[ i ]⟨ liftSeriesOp₂-unfold _+_ f g i 0 ⟩
    Series⟶ℕ→R (ℕ→R⟶Series f + ℕ→R⟶Series g) 0
  ≡⟨ refl ⟩
    f 0 +R g 0
  ∎
+'-compwise-n f g (suc n) = +'-compwise-n (λ n → f (suc n)) (λ n → g (suc n)) n

+'-compwise : ∀ f g → (f +' g) ≡ (λ n → f n +R g n)
+'-compwise f g i n = +'-compwise-n f g n i

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


addp : PathP (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) _+'_ _+_
addp i = transport-filler 
  (λ i → Series≡ℕ→R i → Series≡ℕ→R i → Series≡ℕ→R i) 
  _+_ (~ i)

+'-comm : ∀ f g → f +' g ≡ g +' f
+'-comm =
  transport
    (λ i → (f g : Series≡ℕ→R i) →
      addp (~ i) f g ≡ addp (~ i) g f
    )
    +-comm

+'-assoc : ∀ f g h → f +' (g +' h) ≡ (f +' g) +' h
+'-assoc =
  transport
    (λ i → (f g h : Series≡ℕ→R i) →
      addp (~ i) f (addp (~ i) g h) ≡ addp (~ i) (addp (~ i) f g) h
    )
    +-assoc

+'‿⁺ : ∀ f g → (f +' g) ⁺ ≡ f ⁺ +' g ⁺
+'‿⁺ f g = refl

index-additive : ∀ f g → Series⟶ℕ→R (f + g) ≡ Series⟶ℕ→R f +' Series⟶ℕ→R g
index-additive f g = 
  Series⟶ℕ→R (f + g)
    ≡[ j ]⟨ Series⟶ℕ→R 
            (transport⁻Transport 
                (λ i → Series≡ℕ→R i → Series≡ℕ→R i → Series≡ℕ→R i) _+_ (~ j) f g
            )
    ⟩
  Series⟶ℕ→R (liftℕ→ROp₂ _+'_ f g)
    ≡⟨ cong Series⟶ℕ→R (liftℕ→ROp₂-unfold _+'_ f g) ⟩
  Series⟶ℕ→R (ℕ→R⟶Series (Series⟶ℕ→R f +' Series⟶ℕ→R g))
    ≡⟨ Ser-Nat-sect _ ⟩
  Series⟶ℕ→R f +' Series⟶ℕ→R g
    ∎

index-additive-n : ∀ f g n → (f + g) [ n ] ≡ f [ n ] +R g [ n ]
index-additive-n f g n =
    (f + g) [ n ]
  ≡⟨ cong (λ h → h n) (index-additive f g) ⟩
    (Series⟶ℕ→R f +' Series⟶ℕ→R g) n
  ≡⟨ +'-compwise-n _ _ n ⟩
    f [ n ] +R g [ n ]
  ∎
  
