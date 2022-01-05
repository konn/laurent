{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.CommRing.PowerSeries.Properties {ℓ} (R : CommRing ℓ) where
open import Cubical.Algebra.RingSolver.ReflectionSolving
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

private
  module RingLemmas {ℓ'} (A : CommRing ℓ') where

    open CommRingStr (snd A)
    a+b-b≡a : ∀ a b → a + b - b ≡ a
    a+b-b≡a = solve A

    a≡b+c⇒a-c≡b : ∀ a b c → a ≡ b + c → a - c ≡ b
    a≡b+c⇒a-c≡b a b c a≡b+c = 
      a - c         ≡⟨ cong (_- c) a≡b+c ⟩
      b + c - c     ≡⟨ a+b-b≡a b c ⟩
      b             ∎
    
    [a-b]·c≡a·c-b·c : ∀ a b c → (a - b) · c ≡ a · c - b · c
    [a-b]·c≡a·c-b·c = solve A

    [1-a]·b≡b-b·a : ∀ a b → (1r - a) · b ≡ b - b · a
    [1-a]·b≡b-b·a = solve A

open import Algebra.CommRing.PowerSeries.Base R
open import Algebra.CommRing.PowerSeries.Zip R
open import Algebra.CommRing.PowerSeries.Addition R
open import Algebra.CommRing.PowerSeries.Multiplication R
open import Lemmas.IsoEquiv
open import Cubical.Data.Sigma
open PowerSeries
open import Algebra.Ring.FromNat (CommRing→Ring R)
open import Cubical.Foundations.Powerset
open import Cubical.Data.FinData
open import Cubical.Data.Nat
  using ( ℕ ; suc; _∸_ )
  renaming 
    ( _+_ to _+ℕ_; _·_ to _·ℕ_ ; +-comm to +ℕ-comm 
    ; +-zero to +ℕ-identity-r ; +-suc to +ℕ-suc
    )
open import Cubical.Data.Nat.Order

open CommRingStr (snd R) renaming 
  ( _·_ to _·R_ ; _+_ to _+R_; -_ to -R_; 1r to 1R; 0r to 0R
  ; _-_ to _-R_
  ; +Assoc to +R-assoc
  ; +Comm to +R-comm
  ; +Identity to +R-identity
  ; +Inv to +R-inverse
  ; +Rinv to +R-rinv
  ; ·-comm to ·R-comm
  ; ·Assoc to ·R-assoc
  ; ·Identity to ·R-identity
  ; is-set to R-isSet
  ; ·Rdist+ to R-·Rdist+
  ; ·Ldist+ to R-·Ldist+
  )

open CommRingStr (snd (Series-CommRing)) using (_-_)
open Variables
open RingLemmas Series-CommRing

[1-X]⁻¹ : PowerSeries
[1-X]⁻¹ = repeat 1R

⟦1R⟧≡1s : ⟦ 1R ⟧ ≡ 1s
head (⟦1R⟧≡1s i) = 1R
tail (⟦1R⟧≡1s i) = 0s

[1-X]·[1-X]⁻¹≡1 : (1s - X) · [1-X]⁻¹ ≡ 1s
[1-X]·[1-X]⁻¹≡1 = 
  (1s - X) · [1-X]⁻¹
    ≡⟨ [1-a]·b≡b-b·a X [1-X]⁻¹ ⟩
  [1-X]⁻¹ - tail [1-X]⁻¹ · X
    ≡⟨ a≡b+c⇒a-c≡b [1-X]⁻¹ ⟦ head [1-X]⁻¹ ⟧ (tail [1-X]⁻¹ · X) 
        (sym (isolate-constant [1-X]⁻¹))
    ⟩
  ⟦ head [1-X]⁻¹ ⟧
    ≡⟨ refl ⟩
  ⟦ 1R ⟧
    ≡⟨ ⟦1R⟧≡1s ⟩
  1s
    ∎
