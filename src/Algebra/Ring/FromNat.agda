{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.Ring
module Algebra.Ring.FromNat {ℓ} (R : Ring ℓ) where
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Prelude


open RingStr (snd R)

fromNat : ℕ → ⟨ R ⟩
fromNat 0 = 0r
fromNat 1 = 1r
fromNat (suc n) = 1r + fromNat n

fromNat-suc : ∀ n → fromNat (suc n) ≡ 1r + fromNat n
fromNat-suc 0 = sym (fst (+Identity 1r))
fromNat-suc (suc n) = refl

fromNat-suc-· : ∀ n x → fromNat (suc n) · x ≡ x + fromNat n · x
fromNat-suc-· n x = 
  fromNat (suc n) · x
    ≡⟨ cong (_· x) (fromNat-suc n) ⟩
  (1r + fromNat n) · x
    ≡⟨ ·Ldist+ 1r (fromNat n) x ⟩
  1r · x + fromNat n · x
    ≡⟨ cong (_+ fromNat n · x) (snd (·Identity x)) ⟩
  x + fromNat n · x
    ∎
