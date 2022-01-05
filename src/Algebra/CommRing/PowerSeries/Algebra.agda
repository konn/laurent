{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.CommRing.PowerSeries.Algebra {ℓ} (R : CommRing ℓ) where
open import Algebra.CommRing.PowerSeries.Base R
open import Algebra.CommRing.PowerSeries.Addition R
open import Algebra.CommRing.PowerSeries.Multiplication R
open import Algebra.CommRing.PowerSeries.Module R
open import Lemmas.IsoEquiv
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
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
  ; ·-comm to ·R-comm
  ; ·Assoc to ·R-assoc
  ; ·Identity to ·R-identity
  ; is-set to R-isSet
  ; ·Rdist+ to R-·Rdist+
  ; ·Ldist+ to R-·Ldist+
  )

⋆-lassoc : ∀ r x y → (r ⋆ x) · y ≡ (r ⋆ (x · y))
⋆-lassoc r x y =
    (r ⋆ x) · y 
  ≡⟨ cong (_· y) (sym (⟦r⟧·x≡r⋆x r x)) ⟩
    (⟦ r ⟧ · x) · y
  ≡⟨ sym (·-assoc _ _ _) ⟩
    ⟦ r ⟧ · (x · y)
  ≡⟨ ⟦r⟧·x≡r⋆x r (x · y) ⟩
    r ⋆ (x · y)
  ∎

open import Cubical.Algebra.RingSolver.ReflectionSolving

private
  lem : ∀ {a} (R : CommRing a) → ∀ r x0 y0 → 
    let open CommRingStr (snd R) renaming (_·_ to _·A_)
    in r ·A (x0 ·A y0) ≡ x0 ·A (r ·A y0)
  lem A = solve A

⋆-rassoc : ∀ r x y → r ⋆ (x · y) ≡ x · (r ⋆ y)
⋆-rassoc r x y =
  r ⋆ (x · y) 
    ≡⟨ sym (⟦r⟧·x≡r⋆x r (x · y)) ⟩
  ⟦ r ⟧ · (x · y)
    ≡⟨ lem Series-CommRing ⟦ r ⟧ x y ⟩
  x · (⟦ r ⟧ · y)
    ≡⟨ cong (x ·_) (⟦r⟧·x≡r⋆x r y) ⟩
  x · (r ⋆ y)
    ∎

⋆-isAlgebra : IsAlgebra (CommRing→Ring R) 0s 1s _+_ _·_ -_ _⋆_
⋆-isAlgebra = 
  record 
    { isLeftModule = ⋆-isLeftModule 
    ; ·-isMonoid = ·-IsMonoid
    ; dist = +-·-distrib
    ; ⋆-lassoc  = ⋆-lassoc 
    ; ⋆-rassoc  = ⋆-rassoc 
    }

⋆-isCommAlgebra : IsCommAlgebra R 0s 1s _+_ _·_ -_ _⋆_
⋆-isCommAlgebra = iscommalgebra ⋆-isAlgebra ·-comm

commAlgebraStr : CommAlgebraStr R PowerSeries
commAlgebraStr = commalgebrastr 0s 1s _+_ _·_ -_ _⋆_ ⋆-isCommAlgebra

R-CommAlgebra : CommAlgebra R _
R-CommAlgebra = (_ , commAlgebraStr)
