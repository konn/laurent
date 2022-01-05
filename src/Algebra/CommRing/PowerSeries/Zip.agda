{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
-- | Zip products; i.e. componentwise products.
module Algebra.CommRing.PowerSeries.Zip {ℓ} (R : CommRing ℓ) where
open import Cubical.Algebra.Ring
open import Algebra.CommRing.PowerSeries.Base R
open import Algebra.CommRing.PowerSeries.Addition R
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
open import Algebra.CommRing.PowerSeries.Module R
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

infixl 8 _⊗_ _⊗'_
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

⋆-⊗-dist : ∀ r x y → (r ⋆ x) ⊗ y ≡ r ⋆ (x ⊗ y)
head (⋆-⊗-dist r x y i) = ·R-assoc r (head x) (head y) (~ i)
tail (⋆-⊗-dist r x y i) = ⋆-⊗-dist r (tail x) (tail y) i

⊗-⋆-dist : ∀ x r y → x ⊗ (r ⋆ y) ≡ r ⋆ (x ⊗ y)
head (⊗-⋆-dist x r y i) = lem (head x) r (head y) i
  where
    lem : ∀ a b c → a ·R (b ·R c) ≡ b ·R (a ·R c)
    lem = solve R
tail (⊗-⋆-dist x r y i) = ⊗-⋆-dist (tail x) r (tail y) i


_⊗'_ : (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩)
f ⊗' g = λ n → f n ·R g n

⊗≡⊗'-n : ∀ f g n → ((Series⟶ℕ→R f) ⊗' (Series⟶ℕ→R g)) n ≡ Series⟶ℕ→R (f ⊗ g) n
⊗≡⊗'-n f g 0 = refl
⊗≡⊗'-n f g (suc n) = 
  ((Series⟶ℕ→R f) ⊗' (Series⟶ℕ→R g)) (suc n)
    ≡⟨ refl ⟩
  Series⟶ℕ→R (tail f) n ·R Series⟶ℕ→R (tail g) n
    ≡⟨ refl ⟩
  (Series⟶ℕ→R (tail f) ⊗' Series⟶ℕ→R (tail g)) n
    ≡⟨ ⊗≡⊗'-n (tail f) (tail g) n ⟩
  Series⟶ℕ→R (tail f ⊗ tail g) n
    ≡⟨ refl ⟩
  Series⟶ℕ→R (f ⊗ g) (suc n)
    ∎

⊗≡⊗' : ∀ f g → Series⟶ℕ→R f ⊗' Series⟶ℕ→R g ≡ Series⟶ℕ→R (f ⊗ g)
⊗≡⊗' f g i n = ⊗≡⊗'-n f g n i

zipp : PathP (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) _⊗'_ _⊗_
zipp =
  subst 
    (PathP (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) _⊗'_)
    (funExt (λ f → funExt (λ g →
      transport 
        (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i))
        _⊗'_ f g
        ≡⟨ liftℕ→ROp₂-unfold _⊗'_ f g ⟩
      ℕ→R⟶Series (Series⟶ℕ→R f ⊗' Series⟶ℕ→R g)
        ≡⟨ cong ℕ→R⟶Series (⊗≡⊗' f g) ⟩
      ℕ→R⟶Series (Series⟶ℕ→R (f ⊗ g))
        ≡⟨ Ser-Nat-retr (f ⊗ g) ⟩
      f ⊗ g
        ∎
    )))
    (transport-filler (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) _⊗'_)
