{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.CommRing.PowerSeries.Module {ℓ} (R : CommRing ℓ) where
open import Algebra.CommRing.PowerSeries.Base R
open import Algebra.CommRing.PowerSeries.Addition R
open import Lemmas.IsoEquiv
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Module
open import Cubical.Algebra.Ring.Properties
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

infixr 8.5 _⋆_ _⋆'_
_⋆_ : ⟨ R ⟩ → PowerSeries → PowerSeries
head (c ⋆ f) = c ·R head f
tail (c ⋆ f) = c ⋆ tail f

_⋆'_ : ⟨ R ⟩ → (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩)
c ⋆' f = λ n → c ·R f n

tail-⋆ : ∀ c f → tail (c ⋆ f) ≡ c ⋆ tail f
tail-⋆ c f = refl

private 
  aux₁ : ∀ c y n →
    transport (λ i → ⟨ R ⟩ → Series≡ℕ→R i → Series≡ℕ→R i) _⋆_ c y n
    ≡ (c ⋆' y) n
  aux₁ c y 0 = 
    transport (λ i → ⟨ R ⟩ → Series≡ℕ→R i → Series≡ℕ→R i) _⋆_ c y 0
      ≡⟨ cong (λ x → x 0) (transportIsoToPathOp₁-over Series≃ℕ→R _⋆_ c y) ⟩
    Series⟶ℕ→R (c ⋆ (ℕ→R⟶Series y)) 0
      ≡⟨ refl ⟩
    head (c ⋆ (ℕ→R⟶Series y))
      ≡⟨ refl ⟩
    c ·R y 0
      ≡⟨ refl ⟩
    (c ⋆' y) 0
      ∎
  aux₁ c y (suc n) =
    transport (λ i → ⟨ R ⟩ → Series≡ℕ→R i → Series≡ℕ→R i) _⋆_ c y (suc n)
      ≡⟨ cong (λ x → x (suc n)) (transportIsoToPathOp₁-over Series≃ℕ→R _⋆_ c y) ⟩
    Series⟶ℕ→R (c ⋆ (ℕ→R⟶Series y)) (suc n)
      ≡⟨ refl ⟩
    Series⟶ℕ→R (c ⋆ ℕ→R⟶Series (y ⁺)) n
      ≡⟨ cong (λ h → h n) 
        (sym (transportIsoToPathOp₁-over Series≃ℕ→R _⋆_ c (y ⁺)))
      ⟩
    transport (λ i → ⟨ R ⟩ → Series≡ℕ→R i → Series≡ℕ→R i) _⋆_ c (y ⁺) n
      ≡⟨ aux₁ c (y ⁺) n ⟩
    (c ⋆' (y ⁺)) n
      ≡⟨ refl ⟩
    c ·R y (suc n)
      ≡⟨ refl ⟩
    (c ⋆' y) (suc n)
      ∎

  aux :
    transport (λ i → ⟨ R ⟩ → Series≡ℕ→R i → Series≡ℕ→R i) _⋆_ ≡ _⋆'_
  aux i c y n = aux₁ c y n i

scalarp⁻ : 
  PathP (λ i → ⟨ R ⟩ → Series≡ℕ→R i → Series≡ℕ→R i) _⋆_ _⋆'_
scalarp⁻ =
  subst 
    (PathP (λ i → ⟨ R ⟩ → Series≡ℕ→R i → Series≡ℕ→R i) _⋆_)
    aux
    lem
  where
    lem : PathP (λ i → ⟨ R ⟩ → Series≡ℕ→R i → Series≡ℕ→R i) _⋆_ 
        (transport (λ i → ⟨ R ⟩ → Series≡ℕ→R i → Series≡ℕ→R i) _⋆_)
    lem = transport-filler (λ i → ⟨ R ⟩ → Series≡ℕ→R i → Series≡ℕ→R i) _⋆_

scalarp : PathP (λ i → ⟨ R ⟩ → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) _⋆'_ _⋆_
scalarp i = scalarp⁻ (~ i)

⋆-assoc : ∀ r s x → (r ·R s) ⋆ x ≡ r ⋆ (s ⋆ x)
head (⋆-assoc r s x i) = ·R-assoc r s (head x) (~ i)
tail (⋆-assoc r s x i) = ⋆-assoc r s (tail x) i

⋆-assoc' : ∀ r s x → (r ·R s) ⋆' x ≡ r ⋆' (s ⋆' x)
⋆-assoc' = 
  transport
    (λ i → (r s : ⟨ R ⟩) (x : Series≡ℕ→R i) →
      let _⋆ᵢ_ = scalarp⁻ i
      in (r ·R s) ⋆ᵢ x ≡ r ⋆ᵢ (s ⋆ᵢ x)
    )
    ⋆-assoc

⋆-ldist : ∀ r s x → (r +R s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x)
head (⋆-ldist r s x i) = R-·Ldist+ r s (head x) i
tail (⋆-ldist r s x i) = ⋆-ldist r s (tail x) i

⋆-ldist' : ∀ r s x → (r +R s) ⋆' x ≡ (r ⋆' x) +' (s ⋆' x)
⋆-ldist' =
  transport
    (λ i → (r s : ⟨ R ⟩) (x : Series≡ℕ→R i) →
      let _⋆ᵢ_ = scalarp⁻ i
          _+ᵢ_ = addp (~ i)
      in (r +R s) ⋆ᵢ x  ≡ (r ⋆ᵢ x) +ᵢ (s ⋆ᵢ x)
    )
    ⋆-ldist

⋆-rdist : ∀ r x y → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y)
head (⋆-rdist r x y i) = R-·Rdist+ r (head x) (head y) i
tail (⋆-rdist r x y i) = ⋆-rdist r (tail x) (tail y) i

⋆-rdist' : ∀ r x y → r ⋆' (x +' y) ≡ (r ⋆' x) +' (r ⋆' y)
⋆-rdist' =
  transport
    (λ i → (r : ⟨ R ⟩) (x y : Series≡ℕ→R i) →
      let _⋆ᵢ_ = scalarp⁻ i
          _+ᵢ_ = addp (~ i)
      in r ⋆ᵢ (x +ᵢ y) ≡ (r ⋆ᵢ x) +ᵢ (r ⋆ᵢ y)
    )
    ⋆-rdist


⋆-lid : ∀ x → 1R ⋆ x ≡ x
head (⋆-lid x i) = snd (·R-identity (head x)) i
tail (⋆-lid x i) = ⋆-lid (tail x) i

⋆-isLeftModule : IsLeftModule (CommRing→Ring R) 0s _+_ -_ _⋆_
⋆-isLeftModule = ismodule +-isAbGroup ⋆-assoc ⋆-ldist ⋆-rdist ⋆-lid

moduleStr : LeftModuleStr (CommRing→Ring R) PowerSeries
moduleStr = leftmodulestr 0s _+_ -_ _⋆_ ⋆-isLeftModule

pow-module : LeftModule (CommRing→Ring R) _
pow-module = (_ , moduleStr)

open RingTheory (CommRing→Ring R) 
  renaming
    ( 0RightAnnihilates to 0R-absorb-r
    ; 0LeftAnnihilates to 0R-absorb-l
    )

⋆0s≡0s : ∀ r → r ⋆ 0s ≡ 0s
head (⋆0s≡0s r i) = 0R-absorb-r r i
tail (⋆0s≡0s r i) = ⋆0s≡0s r i

⋆0s≡0s' : ∀ r → r ⋆' 0s' ≡ 0s'
⋆0s≡0s' =
  transport
    (λ i → (r : ⟨ R ⟩) →
      scalarp (~ i) r (zerop (~ i)) ≡ zerop (~ i)
    )
    ⋆0s≡0s

⋆1s≡⟦⟧ : ∀ r → r ⋆ 1s ≡ ⟦ r ⟧
head (⋆1s≡⟦⟧ r i) = fst (·R-identity r) i
tail (⋆1s≡⟦⟧ r i) = ⋆0s≡0s r i

⋆1s≡⟦⟧' : ∀ r → r ⋆' 1s' ≡ ⟦ r ⟧'
⋆1s≡⟦⟧' =
  transport
    (λ i → (r : ⟨ R ⟩) →
      scalarp (~ i) r (onep (~ i)) ≡ ⟦ r ⟧p (~ i)
    )
    ⋆1s≡⟦⟧

⋆-[] : ∀ r x n → (r ⋆ x) [ n ] ≡ r ·R (x [ n ])
⋆-[] r x 0 = refl
⋆-[] r x (suc n) =
  (r ⋆ x) [ suc n ] 
    ≡⟨ refl ⟩ 
  tail (r ⋆ x) [ n ] 
    ≡⟨ refl ⟩
  (r ⋆ tail x ) [ n ]
    ≡⟨ ⋆-[] r (tail x) n ⟩
  r ·R (tail x [ n ])
    ≡⟨ refl ⟩ 
  r ·R (x [ suc n ])
    ∎
