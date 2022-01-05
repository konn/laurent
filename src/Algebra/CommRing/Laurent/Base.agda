{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.CommRing.Laurent.Base {ℓ} (R : CommRing ℓ) where
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Foundations.Prelude
open import Algebra.CommRing.PowerSeries R
open import Algebra.CommRing.Lemmas

-- | We define formal Laurent series _relative to_ a
-- multiplicative subset S as the localisation of
-- the ring R⟦X⟧ of formal power serieses by S.
-- This can be thought as the subring of R((X)) generated by S⁻¹.
-- Classically, this coincides with the usual definition of Laurent Series for
-- R = R ∖ { 0 }, if R is a field
-- (i.e. formal power series admitting a finite number of negative powers).
-- However, constructively, there are several (non-equivalent) definitions of fields and integral domains.
-- Moreover, in some setting (e.g. smooth infinitesimal analysis), the ring ℝ of
-- real numbers FAILS be a field or some of the formalisations of 
-- integral domain.
LaurentSeries : ∀{S} → isMultClosedSubset Series-CommRing S → CommRing _
LaurentSeries {S = S} isClosed = S⁻¹RAsCommRing
  where 
    open Loc Series-CommRing S isClosed
