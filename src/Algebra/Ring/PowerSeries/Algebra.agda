{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.Ring.PowerSeries.Algebra {ℓ} (R : CommRing ℓ) where
open import Algebra.Ring.PowerSeries.Base R
open import Algebra.Ring.PowerSeries.Addition R
open import Algebra.Ring.PowerSeries.Multiplication R
open import Algebra.Ring.PowerSeries.Module R
open import Lemmas.IsoEquiv
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Algebra.Algebra
open import Cubical.Foundations.SIP
open import Cubical.Data.Nat
  using ( ℕ ; suc )
  renaming (_+_ to _+ℕ_; _·_ to _·ℕ_)

open PowerSeries
open import Algebra.Ring.FromNat (CommRing→Ring R)

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
  ; ·Rdist+ to R-·Rdist+
  ; ·Ldist+ to R-·Ldist+
  )

⋆-lassoc-n' : ∀ r x y n → ((r ⋆' x) ·' y) n ≡ (r ⋆' (x ·' y)) n
⋆-lassoc-n' r x y 0 = 
    ((r ⋆' x) ·' y) 0
      ≡⟨ refl ⟩
    (r ·R x 0) ·R y 0
      ≡⟨ sym (·R-assoc r (x 0) (y 0)) ⟩
    r ·R (x 0 ·R y 0)
      ≡⟨ refl ⟩
    (r ⋆' (x ·' y)) 0
      ∎
⋆-lassoc-n' r x y (suc n) = 
    ((r ⋆' x) ·' y) (suc n)
      ≡⟨ refl ⟩
    ((r ⋆' x) ·' y ⁺) n  +R  ((r ⋆' (x  ⁺)) ·' y) n
      ≡⟨ cong₂ _+R_ (⋆-lassoc-n' r x (y ⁺) n) (⋆-lassoc-n' r (x ⁺) y n) ⟩
    (r ⋆' (x ·' y ⁺)) n  +R  (r ⋆' ((x  ⁺) ·' y)) n
      ≡⟨ sym (+'-compwise-n (r ⋆' (x ·' y ⁺)) (r ⋆' ((x  ⁺) ·' y)) n) ⟩
    (r ⋆' (x ·' y ⁺) +' r ⋆' ((x  ⁺) ·' y)) n
      ≡⟨ cong (λ f → f n) (sym (⋆-rdist' r (x ·' y ⁺) ((x  ⁺) ·' y))) ⟩
    (r ⋆' ((x ·' y ⁺) +' ((x  ⁺) ·' y))) n
      ≡⟨ refl ⟩
    r ·R ((x ·' y ⁺) +' ((x ⁺) ·' y)) n
      ≡⟨ cong (r ·R_) (+'-compwise-n (x ·' y ⁺) ((x  ⁺) ·' y) n) ⟩
    r ·R ((x ·' y ⁺) n +R ((x ⁺) ·' y) n)
      ≡⟨ refl ⟩
    (r ⋆' (x ·' y)) (suc n)
      ∎

⋆-lassoc : ∀ r x y → (r ⋆ x) · y ≡ (r ⋆ (x · y))
⋆-lassoc = 
  transport⁻
    (λ i → (r : ⟨ R ⟩) (x y : Series≡ℕ→R i) →
      let _⋆ᵢ_ = scalarp (~ i)
          _·ᵢ_ = mulp (~ i)
      in (r ⋆ᵢ x) ·ᵢ y ≡ (r ⋆ᵢ (x ·ᵢ y))
    )
    (λ r x y i n → ⋆-lassoc-n' r x y n i)

open import Cubical.Algebra.RingSolver.ReflectionSolving

private
  lem : ∀ (r x0 y0 : ⟨ R ⟩) → r ·R (x0 ·R y0) ≡ x0 ·R (r ·R y0)
  lem = solve R

⋆-rassoc'-n : ∀ r x y n → (r ⋆' (x ·' y)) n ≡ (x ·' (r ⋆' y)) n
⋆-rassoc'-n r x y 0 =
  (r ⋆' (x ·' y)) 0
    ≡⟨ refl ⟩
  r ·R (x 0 ·R y 0)
    ≡⟨ lem r (x 0) (y 0) ⟩ 
  x 0 ·R (r ·R y 0) 
    ≡⟨ refl ⟩
  (x ·' (r ⋆' y)) 0
    ∎
⋆-rassoc'-n r x y (suc n) =
  (r ⋆' (x ·' y)) (suc n)
    ≡⟨ refl ⟩
  r ·R ((x ·' y ⁺) n +R (x ⁺ ·' y) n)
    ≡⟨ R-·Rdist+  r ((x ·' y ⁺) n) ((x ⁺ ·' y) n) ⟩
  (r ⋆' (x ·' y ⁺)) n +R (r ⋆' (x ⁺ ·' y)) n
    ≡⟨ cong₂ _+R_ (⋆-rassoc'-n r x (y ⁺) n) (⋆-rassoc'-n r (x ⁺) y n) ⟩
  (x ·' (r ⋆' y)⁺) n +R (x ⁺ ·' (r ⋆' y)) n
    ≡⟨ refl ⟩
  (x ·' (r ⋆' y)) (suc n)
    ∎

⋆-rassoc : ∀ r x y → r ⋆ (x · y) ≡ x · (r ⋆ y)
⋆-rassoc = 
  transport⁻
    (λ i → (r : ⟨ R ⟩) (x y : Series≡ℕ→R i) →
      let _⋆ᵢ_ = scalarp (~ i)
          _·ᵢ_ = mulp (~ i)
      in r ⋆ᵢ (x ·ᵢ y) ≡ x ·ᵢ (r ⋆ᵢ y)
    )
    (λ r x y i n → ⋆-rassoc'-n r x y n i)

⋆-isAlgebra : IsAlgebra (CommRing→Ring R) 0s 1s _+_ _·_ -_ _⋆_
⋆-isAlgebra = 
  record 
    { isLeftModule = ⋆-isLeftModule 
    ; ·-isMonoid = ·-IsMonoid
    ; dist = +-·-distrib
    ; ⋆-lassoc  = ⋆-lassoc 
    ; ⋆-rassoc  = ⋆-rassoc 
    }

algebraStr : AlgebraStr (CommRing→Ring R) PowerSeries
algebraStr = algebrastr 0s 1s _+_ _·_ -_ _⋆_ ⋆-isAlgebra

R-algebra : Algebra (CommRing→Ring R) _
R-algebra = (_ , algebraStr)
