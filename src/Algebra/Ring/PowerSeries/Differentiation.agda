{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.Ring.PowerSeries.Differentiation {ℓ} (R : CommRing ℓ) where
open import Algebra.Ring.PowerSeries.Base R
open import Algebra.Ring.PowerSeries.Addition R
open import Algebra.Ring.PowerSeries.Multiplication R
open import Algebra.Ring.PowerSeries.Module R
open import Cubical.Data.Sigma
open import Cubical.Algebra.RingSolver.ReflectionSolving
open import Cubical.Foundations.Prelude
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
  )

-- | A formal differentiation of formal power series
diff' : (ℕ → ⟨ R ⟩) → ℕ → ⟨ R ⟩
diff' f n = fromNat (suc n) ·R f (suc n)

infixl 10 _′
infixr 10 d/dx_

_′ d/dx_ : PowerSeries → PowerSeries
_′ = transport (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) diff'
d/dx_ = _′
diff = _′

diffp : PathP (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) diff' _′
diffp = transport-filler (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) diff'

diff'-additive-n : ∀ f g n → diff' (f +' g) n ≡ (diff' f +' diff' g) n
diff'-additive-n f g n =
  diff' (f +' g) n
    ≡⟨ refl ⟩
  fromNat (suc n) ·R (f +' g) (suc n)
    ≡⟨ cong (fromNat (suc n) ·R_) (+'-compwise-n f g (suc n)) ⟩ 
  fromNat (suc n) ·R (f (suc n) +R g (suc n))
    ≡⟨ R-·Rdist+ (fromNat (suc n)) (f (suc n)) (g (suc n)) ⟩ 
  fromNat (suc n) ·R f (suc n)  +R  fromNat (suc n) ·R g (suc n)
    ≡⟨ refl ⟩
  diff' f n +R diff' g n
    ≡⟨ sym ((+'-compwise-n (diff' f) (diff' g) n)) ⟩ 
  (diff' f +' diff' g) n
    ∎

diff'-additive : ∀ f g → diff' (f +' g) ≡ diff' f +' diff' g
diff'-additive f g i n = diff'-additive-n f g n i

diff-additive : ∀  f g → (f + g)′ ≡ f ′ + g ′
diff-additive =
  transport 
    (λ i → (f g : Series≡ℕ→R (~ i)) → 
      diffp i (addp i f g) 
        ≡ addp i (diffp i f) (diffp i g)
    )
  diff'-additive

private
  shuffle₁ : ∀ a b c → a ·R (b ·R c) ≡ b ·R (a ·R c)
  shuffle₁ = solve R

diff'-scalar : ∀ c f n → diff' (c ⋆' f) n ≡ (c ⋆' diff' f) n
diff'-scalar c f n = 
  diff' (c ⋆' f) n
    ≡⟨ refl ⟩
  fromNat (suc n) ·R (c ⋆' f) (suc n)
    ≡⟨ refl ⟩
  fromNat (suc n) ·R (c ·R f (suc n))
    ≡⟨ shuffle₁ (fromNat (suc n)) c (f (suc n)) ⟩
  c ·R (fromNat (suc n) ·R f (suc n))
    ≡⟨ refl ⟩
  (c ⋆' diff' f) n
    ∎

diff-scalar : ∀ c f → (c ⋆ f)′ ≡ c ⋆ f ′
diff-scalar =
  transport 
    (λ i → (c : ⟨ R ⟩) → (f : Series≡ℕ→R (~ i)) → 
      diffp i (scalarp i c f) 
        ≡ scalarp i c (diffp i f)
    )
    (λ c f i n → diff'-scalar c f n i)

diff-linear : ∀ a f b g → (a ⋆ f  +  b ⋆ g)′ ≡ a ⋆ f ′ + b ⋆ g ′
diff-linear a f b g =
  (a ⋆ f  +  b ⋆ g) ′
    ≡⟨ diff-additive (a ⋆ f) (b ⋆ g) ⟩
  (a ⋆ f) ′ + (b ⋆ g) ′
    ≡⟨ cong₂ _+_ (diff-scalar a f) (diff-scalar b g) ⟩
  a ⋆ f ′ + b ⋆ g ′
    ∎

diff'-0 : ∀ f → diff' f 0 ≡ f 1
diff'-0 f = snd (·R-identity (f 1))

diff'-⁺-n : ∀ f n → ((diff' f) ⁺) n ≡ (f ⁺ ⁺ +' diff' (f ⁺)) n
diff'-⁺-n f n =
  ((diff' f)⁺) n
    ≡⟨ refl ⟩
  (fromNat (suc (suc n))) ·R (f ⁺) (suc n)
    ≡⟨ fromNat-suc-· (suc n) ((f ⁺) (suc n)) ⟩
  (f ⁺ ⁺) n  +R  (fromNat (suc n)) ·R (f ⁺) (suc n)
    ≡⟨ refl ⟩
  (f ⁺ ⁺) n  +R  diff' (f ⁺) n
    ≡⟨ sym (+'-compwise-n (f ⁺ ⁺) (diff' (f ⁺)) n) ⟩
  (f ⁺ ⁺ +' diff' (f ⁺)) n
    ∎

diff'-⁺ : ∀ f → (diff' f) ⁺ ≡ f ⁺ ⁺ +' diff' (f ⁺)
diff'-⁺ f i n = diff'-⁺-n f n i

leibniz'-n : ∀ f g n → diff' (f ·' g) n ≡ (f ·' diff' g  +'  diff' f ·' g) n
leibniz'-n f g 0 =
  diff' (f ·' g) 0
    ≡⟨ diff'-0 (f ·' g) ⟩
  (f ·' g) 1
    ≡⟨ refl ⟩
  f 0 ·R g 1  +R  f 1 ·R g 0
    ≡⟨ cong₂ _+R_ 
        (cong (f 0 ·R_) (sym (diff'-0 g)))
        (cong (_·R g 0) (sym (diff'-0 f)))
    ⟩
  f 0 ·R diff' g 0  +R  diff' f 0 ·R g 0
    ≡⟨ refl ⟩
  (f ·' diff' g) 0  +R  (diff' f ·' g) 0
    ≡⟨ sym (+'-compwise-n (f ·' diff' g) (diff' f ·' g) 0) ⟩
  (f ·' diff' g  +'  diff' f ·' g) 0
    ∎ 
leibniz'-n f g (suc n) = 
  diff' (f ·' g) (suc n)
    ≡⟨ refl ⟩
  fromNat (suc (suc n)) ·R (f ·' g) (suc (suc n))
    ≡⟨ {!   !} ⟩
  (f ·' g) (suc (suc n)) 
    +R fromNat (suc n) ·R (f ·' g) (suc (suc n))
    ≡⟨ {!   !} ⟩
  ((f ·' (diff' g)⁺) n  +R  (f ⁺ ·' diff' g) n)
    +R  ((diff' f ·' g ⁺) n  +R  ((diff' f) ⁺ ·' g) n)
    ≡⟨ sym (+'-compwise-n (f ·' diff' g) (diff' f ·' g) (suc n)) ⟩
  (f ·' diff' g  +'  diff' f ·' g) (suc n)
    ∎
