{-# OPTIONS --safe --cubical #-}
module Algebra.CommRing.Lemmas where
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Foundations.Powerset

private
  variable
    ℓ ℓ' : Level

UnitsIsMultClosed : ∀ (R : CommRing ℓ) → isMultClosedSubset R (R ˣ)
UnitsIsMultClosed R =
  record 
    { containsOne = RˣContainsOne
    ; multClosed = λ {s = s} {t = t} sInv tInv →
        let instance 
              _ : s ∈ R ˣ
              _ = sInv
              _ : t ∈ R ˣ
              _ = tInv
        in RˣMultClosed s t
    }
  where
    open CommRingStr (snd R)
    open Units R
