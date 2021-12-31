{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.Ring.PowerSeries.Base {ℓ} (R : CommRing ℓ) where
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
  ; is-set to R-isSet
  )

record PowerSeries : Set ℓ where
  coinductive
  constructor _∷_
  field
    head : ⟨ R ⟩
    tail : PowerSeries

open PowerSeries
infixr 9 _∷_

PowerSeries-isSet : isSet PowerSeries
head (PowerSeries-isSet x y x≡y x≡y′ i j) = 
  R-isSet (head x) (head y) (cong head x≡y) (cong head x≡y′) i j
tail (PowerSeries-isSet x y x≡y x≡y′ i j) = 
  PowerSeries-isSet (tail x) (tail y) (cong tail x≡y) (cong tail x≡y′) i j

0s : PowerSeries
head 0s = 0R
tail 0s = 0s

1s : PowerSeries
head 1s = 1R
tail 1s = 0s

Series⟶ℕ→R : PowerSeries → (ℕ → ⟨ R ⟩)
Series⟶ℕ→R f 0 = head f
Series⟶ℕ→R f (suc n) = Series⟶ℕ→R (tail f) n

ℕ→R⟶Series : (ℕ → ⟨ R ⟩) → PowerSeries
head (ℕ→R⟶Series f) = f 0
tail (ℕ→R⟶Series f) = ℕ→R⟶Series (λ n → f (suc n))

Ser-Nat-sect : ∀ b → Series⟶ℕ→R (ℕ→R⟶Series b) ≡ b
Ser-Nat-sect f i 0 = f 0
Ser-Nat-sect f i (suc n) = Ser-Nat-sect (λ n → f (suc n)) i n

Ser-Nat-retr : ∀ (f : PowerSeries) → ℕ→R⟶Series (Series⟶ℕ→R f) ≡ f
head (Ser-Nat-retr f i) = head f
tail (Ser-Nat-retr f i) = Ser-Nat-retr (tail f) i

Series≃ℕ→R : Iso PowerSeries (ℕ → ⟨ R ⟩)
Series≃ℕ→R = iso Series⟶ℕ→R ℕ→R⟶Series Ser-Nat-sect Ser-Nat-retr

Series≡ℕ→R : PowerSeries ≡ (ℕ → ⟨ R ⟩)
Series≡ℕ→R = isoToPath Series≃ℕ→R

liftℕ→ROp₂ : ((ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩)) → PowerSeries → PowerSeries → PowerSeries
liftℕ→ROp₂ = transport⁻ (λ i → Series≡ℕ→R i → Series≡ℕ→R i → Series≡ℕ→R i)

liftℕ→ROp₂-unfold : 
  ∀(f : (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩)) x y
  → liftℕ→ROp₂ f x y ≡ ℕ→R⟶Series (f (Series⟶ℕ→R x) (Series⟶ℕ→R y))
liftℕ→ROp₂-unfold = transport⁻IsoToPathOp₂ Series≃ℕ→R

liftSeriesOp₂ : (PowerSeries → PowerSeries → PowerSeries)
  → (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩)
liftSeriesOp₂ = transport (λ i → Series≡ℕ→R i → Series≡ℕ→R i → Series≡ℕ→R i)

liftSeriesOp₂-unfold : 
  ∀(f : PowerSeries → PowerSeries → PowerSeries) x y
  → liftSeriesOp₂ f x y ≡ Series⟶ℕ→R (f (ℕ→R⟶Series x) (ℕ→R⟶Series y))
liftSeriesOp₂-unfold = transportIsoToPathOp₂ Series≃ℕ→R

infixl 10 _⁺
_⁺ : (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩)
(f ⁺) n = f (suc n)

tail-to-⁺ : ∀ f → tail (ℕ→R⟶Series f) ≡ ℕ→R⟶Series (f ⁺)
tail-to-⁺ f = refl

⁺-to-tail : ∀ f → (Series⟶ℕ→R f) ⁺ ≡ Series⟶ℕ→R (tail f)
⁺-to-tail f = refl

module Variables where
  X : PowerSeries
  head X = 0R
  head (tail X) = 1R
  tail (tail X) = 0s

  infix 9 X^_
  X^_ : ℕ → PowerSeries
  X^ 0 = 1s
  X^ suc n = 0R ∷ X^ n
