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

1s' : ℕ → ⟨ R ⟩
1s' 0 = 1R
1s' (suc n) = 0R

0s' : ℕ → ⟨ R ⟩
0s' n = 0R

0s'≡0s : 0s' ≡ Series⟶ℕ→R 0s
0s'≡0s i 0 = 0R
0s'≡0s i (suc n) = 0s'≡0s i n

1s'≡1s : 1s' ≡ Series⟶ℕ→R 1s
1s'≡1s i 0 = 1R
1s'≡1s i (suc n) = 0s'≡0s i n

onepInv : PathP (λ i → Series≡ℕ→R i) 1s 1s'
onepInv = subst (PathP (λ i → Series≡ℕ→R i) 1s) 
  (  
  transport Series≡ℕ→R 1s
    ≡[ i ]⟨ transport-isoToPath Series≃ℕ→R i  1s  ⟩
  Series⟶ℕ→R 1s
    ≡⟨ sym 1s'≡1s ⟩
  1s'
    ∎
  )
  onepInvAux
  where
    onepInvAux : PathP (λ i → Series≡ℕ→R i) 1s (transport Series≡ℕ→R  1s)
    onepInvAux = transport-filler Series≡ℕ→R 1s

onep : PathP (λ i → Series≡ℕ→R (~ i)) 1s' 1s
onep i = onepInv (~ i)

zeropInv : PathP (λ i → Series≡ℕ→R i) 0s 0s'
zeropInv = subst (PathP (λ i → Series≡ℕ→R i) 0s)
  (  
  transport Series≡ℕ→R 0s
    ≡[ i ]⟨ transport-isoToPath Series≃ℕ→R i  0s  ⟩
  Series⟶ℕ→R 0s
    ≡⟨ sym 0s'≡0s ⟩
  0s'
    ∎
  )
  onepInvAux
  where
    onepInvAux : PathP (λ i → Series≡ℕ→R i) 0s (transport Series≡ℕ→R  0s)
    onepInvAux = transport-filler Series≡ℕ→R 0s

zerop : PathP (λ i → Series≡ℕ→R (~ i)) 0s' 0s
zerop i = zeropInv (~ i)

⟦_⟧ : ⟨ R ⟩ → PowerSeries
head ⟦ x ⟧ = x
tail ⟦ x ⟧ = 0s

⟦_⟧' : ⟨ R ⟩ → (ℕ → ⟨ R ⟩)
⟦ x ⟧' 0 = x
⟦ x ⟧' (suc n) = 0R

⟦_⟧'≡⟦⟧ : ∀ x → ⟦ x ⟧' ≡ Series⟶ℕ→R ⟦ x ⟧
⟦ x ⟧'≡⟦⟧ i 0 = x
⟦ x ⟧'≡⟦⟧ i (suc n) = 0s'≡0s i n

⟦_⟧pInv : ∀ x → PathP (λ i → Series≡ℕ→R i) ⟦ x ⟧ ⟦ x ⟧'
⟦ x ⟧pInv = subst (PathP (λ i → Series≡ℕ→R i) ⟦ x ⟧) 
  (  
  transport Series≡ℕ→R ⟦ x ⟧
    ≡[ i ]⟨ transport-isoToPath Series≃ℕ→R i  ⟦ x ⟧ ⟩
  Series⟶ℕ→R ⟦ x ⟧
    ≡⟨ sym ⟦ x ⟧'≡⟦⟧ ⟩
  ⟦ x ⟧'
    ∎
  )
  onepInvAux
  where
    onepInvAux : PathP (λ i → Series≡ℕ→R i) ⟦ x ⟧ (transport Series≡ℕ→R ⟦ x ⟧)
    onepInvAux = transport-filler Series≡ℕ→R ⟦ x ⟧

⟦_⟧p : ∀ x → PathP (λ i → Series≡ℕ→R (~ i)) ⟦ x ⟧' ⟦ x ⟧
⟦ x ⟧p i = ⟦ x ⟧pInv (~ i)

tailpInv : PathP (λ i → Series≡ℕ→R i → Series≡ℕ→R i) tail _⁺
tailpInv =
  subst (PathP (λ i → Series≡ℕ→R i → Series≡ℕ→R i) tail) 
    (funExt 
      (λ f →
          transport (λ i → Series≡ℕ→R i → Series≡ℕ→R i) tail f
            ≡⟨ transportIsoToPathOp₁ Series≃ℕ→R tail f ⟩
          Series⟶ℕ→R (tail (ℕ→R⟶Series f))
            ≡⟨ refl ⟩
          Series⟶ℕ→R (ℕ→R⟶Series (f ⁺))
            ≡⟨ Ser-Nat-sect (f ⁺) ⟩
          f ⁺
            ∎
      )
    )
    (transport-filler (λ i → Series≡ℕ→R i → Series≡ℕ→R i) tail)

tailp : PathP (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) _⁺ tail
tailp i = tailpInv (~ i)

module Variables where
  X : PowerSeries
  head X = 0R
  tail X = 1s

  infix 9 X^_
  X^_ : ℕ → PowerSeries
  X^ 0 = 1s
  X^ suc n = 0R ∷ X^ n

  X' : ℕ → ⟨ R ⟩
  X' 0 = 0R
  X' (suc n) = 1s' n

  XpInv : PathP (λ i → Series≡ℕ→R i) X X'
  XpInv = subst (PathP (λ i → Series≡ℕ→R i) X)
    (
      transport Series≡ℕ→R X
        ≡[ i ]⟨ transport-isoToPath Series≃ℕ→R i X ⟩
      Series⟶ℕ→R X
        ≡⟨ funExt 
          (λ  { 0 → refl
              ; (suc n) → λ i → 1s'≡1s (~ i) n
              }
          )
        ⟩
      X'
        ∎
      )
    (transport-filler Series≡ℕ→R X)

  Xp : PathP (λ i → Series≡ℕ→R (~ i)) X' X
  Xp i = XpInv (~ i)
