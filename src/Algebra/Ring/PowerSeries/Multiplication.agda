{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.Ring.PowerSeries.Multiplication {ℓ} (R : CommRing ℓ) where
open import Algebra.Ring.PowerSeries.Base R
open import Algebra.Ring.PowerSeries.Addition R
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.RingSolver.ReflectionSolving
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.Ring.Properties
open import Cubical.Data.Nat
  using ( ℕ ; suc )
  renaming (_+_ to _+ℕ_; _·_ to _·ℕ_)

open PowerSeries

open CommRingStr (snd R) renaming 
  ( _·_ to _·R_ ; _+_ to _+R_; 1r to 1R; 0r to 0R
  ; +Assoc to +R-assoc
  ; +Identity to +R-identity
  ; +Comm to +R-comm
  ; ·Assoc to ·R-assoc
  ; ·-comm to ·R-comm
  ; ·Identity to ·R-identity
  ; is-set to R-isSet
  ; ·Rdist+ to R-·Rdist+
  )

infixl 10 _⁺
_⁺ : (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩)
(f ⁺) n = f (suc n)

infixl 8 _·ℕ→_ _·'_
_·ℕ→_ : (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩)
_·ℕ→_ f g 0 = f 0 ·R g 0
_·ℕ→_ f g (suc n) = 
  (f ·ℕ→ g ⁺) n +R (f ⁺ ·ℕ→ g) n

_·'_ = _·ℕ→_

·ℕ→-curry : ∀ f g n → (f ·ℕ→ g) (suc n) ≡ (f ·ℕ→ g ⁺ +ℕ→ f ⁺ ·ℕ→ g) n
·ℕ→-curry f g n =
    (f ·ℕ→ g) (suc n) 
  ≡⟨ sym (+ℕ→-compwise-n (f ·ℕ→ g ⁺) (f ⁺ ·ℕ→ g) n) ⟩ 
    (f ·ℕ→ g ⁺ +ℕ→ f ⁺ ·ℕ→ g) n
  ∎

·ℕ→‿⁺ : ∀ f g → (f ·ℕ→ g)⁺ ≡ (f ·ℕ→ g ⁺ +ℕ→ f ⁺ ·ℕ→ g)
·ℕ→‿⁺ f g i n = ·ℕ→-curry f g n i

infixl 8 _·_
_·_ : PowerSeries → PowerSeries → PowerSeries
_·_ = liftℕ→ROp₂ _·ℕ→_

infixl 7 _+'_
_+'_ = _+ℕ→_

+ℕ‿⁺ : ∀ f g → (f +' g)⁺ ≡ f ⁺ +' g ⁺
+ℕ‿⁺ f g = refl

·'-comm-n : ∀ f g n → (f ·' g) n ≡ (g ·' f) n
·'-comm-n f g 0 = 
  (f ·' g) 0
    ≡⟨ refl ⟩
  f 0 ·R g 0
    ≡⟨ ·R-comm (f 0) (g 0) ⟩
  g 0 ·R f 0
    ≡⟨ refl ⟩
  (g ·' f) 0
    ∎
·'-comm-n f g (suc n) = 
  (f ·' g) (suc n)
    ≡⟨ refl ⟩
  (f ·' g ⁺) n  +R  (f ⁺ ·' g) n
    ≡⟨ +R-comm ((f ·' g ⁺) n) ((f ⁺ ·' g) n) ⟩
  (f ⁺ ·' g) n  +R  (f ·' g ⁺) n
    ≡⟨ cong₂ _+R_ (·'-comm-n (f ⁺) g n) (·'-comm-n f (g ⁺) n) ⟩
  (g ·' f ⁺) n  +R  (g ⁺ ·' f) n
    ≡⟨ refl ⟩
  (g ·' f) (suc n)
    ∎

·'-comm : ∀ f g → f ·' g ≡ g ·' f
·'-comm f g i n = ·'-comm-n f g n i

·'‿+'-distrib-l-n : ∀ f g h n → (f ·' (g +' h)) n ≡ (f ·' g  +'  f ·' h) n
·'‿+'-distrib-l-n  f g h 0 =
  (f ·' (g +' h)) 0
    ≡⟨ refl ⟩
  f 0 ·R ((g +' h) 0) 
    ≡⟨ cong (f 0 ·R_) (+ℕ→-compwise-n g h 0) ⟩
  f 0 ·R (g 0 +R h 0) 
    ≡⟨ R-·Rdist+ (f 0) (g 0) (h 0) ⟩
  f 0 ·R g 0 +R f 0 ·R h 0
    ≡⟨ refl ⟩ 
  (f ·' g) 0 +R (f ·' h) 0
    ≡⟨ sym (+ℕ→-compwise-n (f ·' g ) (f ·' h) 0) ⟩ 
  (f ·' g  +'  f ·' h) 0
    ∎
·'‿+'-distrib-l-n f g h (suc n) = 
  (f ·' (g +' h)) (suc n) 
    ≡⟨ refl ⟩
  (f ·' (g +' h)⁺) n  +R  (f ⁺ ·' (g +' h)) n
    ≡⟨ refl ⟩
  (f ·' (g ⁺ +' h ⁺)) n  +R  (f ⁺ ·' (g +' h)) n
    ≡⟨ cong₂ _+R_
        (·'‿+'-distrib-l-n f (g ⁺) (h ⁺) n)
        (·'‿+'-distrib-l-n (f ⁺) g h n)
    ⟩
  (f ·' g ⁺ +' f ·' h ⁺) n  +R  (f ⁺ ·' g +' f ⁺ ·' h) n
    ≡⟨ cong₂ _+R_ 
        (+ℕ→-compwise-n (f ·' g ⁺) (f ·' h ⁺) n)
        (+ℕ→-compwise-n (f ⁺ ·' g) (f ⁺ ·' h) n)
      ⟩
  ((f ·' g ⁺) n +R (f ·' h ⁺) n)  +R  ((f ⁺ ·' g) n +R (f ⁺ ·' h) n)
    ≡⟨ lem1 ((f ·' g ⁺) n) ((f ·' h ⁺) n) ((f ⁺ ·' g) n) ((f ⁺ ·' h) n) ⟩
  ((f ·' g ⁺) n +R (f ⁺ ·' g) n)  +R  ((f ·' h ⁺) n +R (f ⁺ ·' h) n)
    ≡⟨ refl ⟩
  (f ·' g) (suc n)  +R  (f ·' h) (suc n)
    ≡⟨ sym (+ℕ→-compwise-n (f ·' g) (f ·' h) (suc n)) ⟩
  (f ·' g  +'  f ·' h) (suc n)
    ∎
  where
    lem1 : ∀ fg⁺ fh⁺ f⁺g f⁺h
      → (fg⁺ +R fh⁺) +R (f⁺g +R f⁺h) ≡ (fg⁺ +R f⁺g) +R (fh⁺ +R f⁺h)
    lem1 = solve R
  
·'‿+'-distrib-l : ∀ f g h → (f ·' (g +' h)) ≡ (f ·' g  +'  f ·' h)
·'‿+'-distrib-l f g h i n = ·'‿+'-distrib-l-n f g h n i

·'‿+'-distrib-r : ∀ f g h → ((f +' g) ·' h) ≡ (f ·' h  +'  g ·' h)
·'‿+'-distrib-r f g h = 
    ((f +' g) ·' h)
  ≡⟨ ·'-comm (f +' g) h ⟩
    h ·' (f +' g)
  ≡⟨ ·'‿+'-distrib-l h f g ⟩
    h ·' f +' h ·' g
  ≡⟨ cong₂ _+'_ (·'-comm h f) (·'-comm h g) ⟩
    f ·' h  +'  g ·' h
  ∎

·'-assoc-n : ∀ f g h n → (f ·ℕ→ (g ·ℕ→ h)) n ≡ ((f ·ℕ→ g) ·ℕ→ h) n
·'-assoc-n f g h 0 = ·R-assoc (f 0) (g 0) (h 0)
·'-assoc-n f g h (suc n) = 
  (f ·ℕ→ (g ·' h)) (suc n)
    ≡⟨ refl ⟩
  (f ·ℕ→ (g ·' h)⁺) n +R (f ⁺ ·' (g ·' h)) n
    ≡⟨ cong (λ x → (f ·' x) n +R (f ⁺ ·' (g ·' h)) n) (·ℕ→‿⁺ g h) ⟩
  (f ·' ((g ·' h ⁺) +' (g ⁺ ·' h))) n +R (f ⁺ ·' (g ·' h)) n
    ≡⟨ cong (_+R (f ⁺ ·' (g ·' h)) n) 
        (·'‿+'-distrib-l-n f (g ·' h ⁺) (g ⁺ ·' h) n)
    ⟩
  (f ·' (g ·' h ⁺) +' f ·' (g ⁺ ·' h)) n +R (f ⁺ ·' (g ·' h)) n
    ≡⟨ cong (_+R (f ⁺ ·' (g ·' h)) n)  
        (+ℕ→-compwise-n (f ·' (g ·' h ⁺)) (f ·' (g ⁺ ·' h)) n)
    ⟩
  (f ·' (g ·' h ⁺)) n +R (f ·' (g ⁺ ·' h)) n +R (f ⁺ ·' (g ·' h)) n
    ≡⟨ sym (+R-assoc ((f ·' (g ·' h ⁺)) n) ((f ·' (g ⁺ ·' h)) n) ((f ⁺ ·' (g ·' h)) n)) ⟩
  (f ·' (g ·' h ⁺)) n +R ((f ·' (g ⁺ ·' h)) n  +R  (f ⁺ ·' (g ·' h)) n)
    ≡⟨ cong ((f ·' (g ·' h ⁺)) n +R_)
        ( (f ·' (g ⁺ ·' h)) n  +R (f ⁺ ·' (g ·' h)) n
            ≡⟨ cong₂ _+R_ 
                (·'-assoc-n f (g ⁺) h n) 
                (·'-assoc-n (f ⁺) g h n)
              ⟩
          ((f ·' g ⁺) ·' h) n  +R ((f ⁺ ·' g) ·' h) n
            ≡⟨ sym (+ℕ→-compwise-n ((f ·' g ⁺) ·' h) ((f ⁺ ·' g) ·' h) n) ⟩
          ((f ·' g ⁺) ·' h  +'  (f ⁺ ·' g) ·' h) n
            ≡[ i ]⟨ ·'‿+'-distrib-r (f ·' g ⁺) (f ⁺ ·' g) h (~ i) n ⟩
          ((f ·' g ⁺  +'  f ⁺ ·' g) ·' h) n
            ≡⟨ sym (cong (λ x → (x ·' h) n) (·ℕ→‿⁺ f g)) ⟩
          ((f ·' g)⁺ ·' h) n
            ∎
        )
    ⟩
  (f ·' (g ·' h ⁺)) n +R ((f ·' g)⁺ ·' h) n
    ≡⟨ cong (_+R ((f ·' g)⁺ ·' h) n) (·'-assoc-n f g (h ⁺) n) ⟩
  ((f ·' g) ·' h ⁺) n +R ((f ·' g)⁺ ·' h) n
    ≡⟨ refl ⟩
  ((f ·' g) ·' h) (suc n)
    ∎

·'-assoc : ∀ f g h → f ·' (g ·' h) ≡ (f ·' g) ·' h
·'-assoc f g h i n = ·'-assoc-n f g h n i

1s' : ℕ → ⟨ R ⟩
1s' = transport Series≡ℕ→R 1s

open RingTheory (CommRing→Ring R) 
  renaming
    ( 0RightAnnihilates to 0R-absorb-r
    ; 0LeftAnnihilates to 0R-absorb-l
    )

·-head : ∀ f g → head (f · g) ≡ head f ·R head g
·-head f g =
  head (f · g) 
    ≡⟨ cong head (liftℕ→ROp₂-unfold _·'_ f g ) ⟩
  head (ℕ→R⟶Series (Series⟶ℕ→R f ·' Series⟶ℕ→R  g))
    ≡⟨ refl ⟩
  (Series⟶ℕ→R f ·' Series⟶ℕ→R  g) 0
    ≡⟨ refl ⟩
  Series⟶ℕ→R f 0 ·R Series⟶ℕ→R g 0
    ≡⟨ refl ⟩
  head f ·R head g
    ∎
