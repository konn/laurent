{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.Ring.PowerSeries {ℓ} (R : CommRing ℓ) where
open import Cubical.Data.Sigma
open import Cubical.Foundations.SIP
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
  using ( ℕ ; suc )
  renaming (_+_ to _+ℕ_; _·_ to _·ℕ_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.RingSolver.ReflectionSolving
open import Lemmas.IsoEquiv

open CommRingStr (snd R) renaming 
  ( _·_ to _·R_ ; _+_ to _+R_; 1r to 1R; 0r to 0R
  ; +Assoc to +R-assoc
  ; +Identity to +R-identity
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
_+ℕ→_ = transport (λ i → Series≡ℕ→R i → Series≡ℕ→R i → Series≡ℕ→R i) _+_

_+ᵢ_ : PathP (λ i → Series≡ℕ→R i → Series≡ℕ→R i → Series≡ℕ→R i) _+_ _+ℕ→_
_+ᵢ_ i = transp (λ j → Series≡ℕ→R (i ∧ j) → Series≡ℕ→R (i ∧ j) → Series≡ℕ→R (i ∧ j))
  (~ i) _+_

+ℕ→-compwise-n : ∀ f g n → (f +ℕ→ g) n ≡ f n +R g n
+ℕ→-compwise-n f g 0 =  
    (f +ℕ→ g) 0
  ≡⟨ cong (λ h → h 0) (transportIsoToPathOp₂ Series≃ℕ→R _+_  f  g ) ⟩
    Series⟶ℕ→R (ℕ→R⟶Series f + ℕ→R⟶Series g) 0
  ≡⟨ refl ⟩
    f 0 +R g 0
  ∎
+ℕ→-compwise-n f g (suc n) = +ℕ→-compwise-n (λ n → f (suc n)) (λ n → g (suc n)) n

+ℕ→-compwise : ∀ f g → (f +ℕ→ g) ≡ (λ n → f n +R g n)
+ℕ→-compwise f g i n = +ℕ→-compwise-n f g n i

{- 
·ℕ→-assoc : ∀ f g h → _·ℕ→_ f (_·ℕ→_ g h) ≡ _·ℕ→_ (_·ℕ→_ f g) h
·ℕ→-assoc f g h i 0 = ·R-assoc (f 0) (g 0) (h 0) i
·ℕ→-assoc f g h i (suc n) = 
    (_·ℕ→_ f (λ n → (_·ℕ→_ g h) (suc n)) n 
      +R _·ℕ→_ (λ n → f (suc n)) (_·ℕ→_ g h) n
  ≡⟨ {! refl  !} ⟩
    (_·ℕ→_ f 
      (λ m → _·ℕ→_ g (λ n → h (suc n)) m +R _·ℕ→_ (λ n → g (suc n)) h ) 
      n 
      +R _·ℕ→_ (λ n → f (suc n)) (_·ℕ→_ g h) n
  ≡⟨ ? ⟩
      _·ℕ→_ (_·ℕ→_ f g) (λ n → h (suc n)) n 
    +R _·ℕ→_ (λ n → (_·ℕ→_ f g) (suc n)) h n
  ∎)
  i 
 -}
{- 
infixl 8 _·ℕ→_
_·ℕ→_ : (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩)
_·ℕ→_ f g 0 = f 0 ·R g 0
_·ℕ→_ f g (suc n) = 
  _·ℕ→_ f (λ n → g (suc n)) n +R _·ℕ→_ (λ n → f (suc n)) g n


infixl 8 _·_
_·_ : PowerSeries → PowerSeries → PowerSeries
_·_ = transport (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) _·ℕ→_


convPath : PathP (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) _·ℕ→_ _·_
convPath i = transp (λ j → Series≡ℕ→R (~ i ∨ ~ j) → Series≡ℕ→R (~ i ∨ ~ j) → Series≡ℕ→R (~ i ∨ ~ j)) (~ i) _·ℕ→_

·-head-tail : ∀ f g → f · g ≡ (head f ·R head g) ∷ (f · tail g + tail f · g)
head (·-head-tail f g i) = {!   !}
tail (·-head-tail f g i) =  {!   !}


{- 
_·_ : PowerSeries → PowerSeries i → PowerSeries i
head (l · r) = head l ·R head r
tail (l · r) = (tail l · r) + (head l ⊗ tail r)
 -}
+-assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
head (+-assoc x y z i) = +R-assoc (head x) (head y) (head z) i
tail (+-assoc x y z i) = +-assoc (tail x) (tail y) (tail z) i

{- 





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
 -}
private
  lemma1 : (a₀ a₁ b₀ b₁ c₀ c₁ : ⟨ R ⟩) →  a₀ ·R (b₀ ·R c₁  +R  b₁ ·R c₀) +R a₁ ·R (b₀ ·R c₀)
              ≡ (a₀ ·R b₀) ·R c₁  +R  (a₀ ·R b₁  +R  a₁ ·R b₀) ·R c₀
  lemma1 = solve R
{- 
·-tail : ∀ x y → tail (x · y) ≡ ((head x ·R head (tail y) +R head (tail x) ·R head y) ∷ (tail x · tail y))
head (·-tail x y i) = refl {x = head (tail (x · y))} i
tail (·-tail x y i) = refl {x = tail (tail (x · y))} i

·-assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
head (·-assoc x y z i) = ·R-assoc (head x) (head y) (head z) i
head (tail (·-assoc x y z i)) =
  let x₀ = head x
      x₁ = head (tail x)
      y₀ = head y
      y₁ = head (tail y)
      z₀ = head z
      z₁ = head (tail z)
  in  lemma1 x₀ x₁ y₀ y₁ z₀ z₁ i
tail (tail (·-assoc x y z i)) = 
  let x₀ = head x
      x₁ = head (tail x)
      y₀ = head y
      y₁ = head (tail y)
      z₀ = head z
      z₁ = head (tail z)
  in  
    (   tail x · tail (y · z)
      ≡⟨ cong (tail x ·_) (·-tail y z) ⟩
        tail x · ( (y₀ ·R z₁ +R y₁ ·R z₀) ∷ (tail y · tail z))
      ≡⟨ ? ⟩
        (x₁ ·R (y₀ ·R z₁ +R y₁ ·R z₀))
          ∷ (x₁ ·R head (tail y · tail z) +R head (tail (tail x)) ·R (y₀ ·R z₁ +R y₁ ·R z₀)) 
          ∷ (tail x · (tail y · tail z))
      ≡⟨ ? ⟩
        (x₁ ·R (y₀ ·R z₁) +R x₁ ·R (y₁ ·R z₀))
          ∷ (x₁ ·R (y₁ · z₁) +R head (tail (tail x)) ·R (y₀ ·R z₁ +R y₁ ·R z₀)) 
          ∷ (tail x · (tail y · tail z))
      ≡⟨ {!   !} ⟩
        ( (x₀ ·R y₁ +R x₁ ·R y₀) ∷ (tail x · tail y)) 
          · tail z
      ≡⟨ sym (cong (_· tail z) (·-tail x y)) ⟩
        tail (x · y) · tail z
      ∎
    ) i
 -} -}