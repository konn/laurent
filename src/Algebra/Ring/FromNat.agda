{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.Ring
module Algebra.Ring.FromNat {ℓ} (R : Ring ℓ) where
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.Foundations.SIP


open RingStr (snd R)

fromNat : ℕ → ⟨ R ⟩
fromNat 0 = 0r
fromNat 1 = 1r
fromNat (suc n) = 1r + fromNat n
