{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.Ring.PowerSeries.Multiplication {ℓ} (R : CommRing ℓ) where
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps
open import Algebra.Ring.PowerSeries.Base R
open import Algebra.Ring.PowerSeries.Addition R
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.RingSolver.ReflectionSolving
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.Ring.Properties
open import Algebra.Ring.PowerSeries.Module R
open import Cubical.Data.Nat
  using ( ℕ ; suc ; ∸-cancelʳ )
  renaming (_+_ to _+ℕ_; _·_ to _·ℕ_; _∸_ to _-ℕ_)
open import Lemmas.IsoEquiv
open PowerSeries

open CommRingStr (snd R) renaming 
  ( _·_ to _·R_ ; _+_ to _+R_; 1r to 1R; 0r to 0R
  ; _-_ to _-R_; -_ to -R_
  ; +Assoc to +R-assoc
  ; +Identity to +R-identity
  ; +Comm to +R-comm
  ; ·Assoc to ·R-assoc
  ; ·-comm to ·R-comm
  ; ·Identity to ·R-identity
  ; is-set to R-isSet
  ; ·Rdist+ to R-·Rdist+
  ; ·Ldist+ to R-·Ldist+
  )

infixl 8 _·'_ _·_
_·'_ : (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩)
(f ·' g) 0 = f 0 ·R g 0
(f ·' g) (suc n) = (f 0 ⋆' g ⁺) n +R (f ⁺ ·' g) n

_·_ : PowerSeries → PowerSeries → PowerSeries
_·_ = liftℕ→ROp₂ _·'_

mulp : PathP (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) _·'_ _·_
mulp i = 
  transp (λ j → Series≡ℕ→R (~ i ∨ ~ j) → Series≡ℕ→R (~ i ∨ ~ j) → Series≡ℕ→R (~ i ∨ ~ j)) (~ i) _·'_

·'-curry : ∀ f g n → (f ·' g) (suc n) ≡ (f 0 ⋆' g ⁺ +' f ⁺ ·' g) n
·'-curry f g n =
    (f ·' g) (suc n) 
  ≡⟨ sym (+'-compwise-n (f 0 ⋆' g ⁺) (f ⁺ ·' g) n) ⟩ 
    (f 0 ⋆' g ⁺ +' f ⁺ ·' g) n
  ∎

·'‿⁺ : ∀ f g → (f ·' g)⁺ ≡ (f 0 ⋆' g ⁺ +' f ⁺ ·' g)
·'‿⁺ f g i n = ·'-curry f g n i

open Variables

open RingTheory (CommRing→Ring R) 
  renaming
    ( 0RightAnnihilates to 0R-absorb-r
    ; 0LeftAnnihilates to 0R-absorb-l
    )

·'-X'-n : ∀ f n → (⟦ f 0 ⟧' +' (f ⁺) ·' X') n ≡ f n
·'-X'-n f 0 = 
  (⟦ f 0 ⟧'  +' (f ⁺) ·' X') 0
    ≡⟨ +'-compwise-n ⟦ f 0 ⟧' ((f ⁺) ·' X') 0 ⟩
  f 0  +R  (f 1 ·R 0R)
    ≡⟨ cong (f 0 +R_) (0R-absorb-r (f 1)) ⟩
  f 0  +R  0R
    ≡⟨ fst (+R-identity (f 0)) ⟩
  f 0
    ∎
·'-X'-n f 1 =
  (⟦ f 0 ⟧' +' (f ⁺) ·' X') 1
    ≡⟨ +'-compwise-n ⟦ f 0 ⟧' ((f ⁺) ·' X') 1 ⟩
  0R  +R  ((f ⁺) ·' X') 1
    ≡⟨ snd (+R-identity (((f ⁺) ·' X') 1)) ⟩
  ((f ⁺) ·' X') (suc 0)
    ≡⟨ refl ⟩
  f 1 ·R 1R +R f 2 ·R 0R
    ≡⟨ cong₂ _+R_ (fst (·R-identity (f 1))) (0R-absorb-r (f 2)) ⟩
  f 1 +R 0R
    ≡⟨ fst (+R-identity (f 1)) ⟩
  f 1
    ∎
·'-X'-n f (suc (suc n)) =
  (⟦ f 0 ⟧' +' (f ⁺) ·' X') (suc (suc n))
    ≡⟨ +'-compwise-n ⟦ f 0 ⟧' ((f ⁺) ·' X') (suc (suc n)) ⟩
  0R +R ((f ⁺) ·' X') (suc (suc n))
    ≡⟨ snd (+R-identity (((f ⁺) ·' X') (suc (suc n)))) ⟩
  ((f ⁺) ·' X') (suc (suc n))
    ≡⟨ refl ⟩
  f 1 ·R 0R +R (f ⁺ ⁺ ·' X') (suc n)
    ≡⟨ cong (_+R (f ⁺ ⁺ ·' X') (suc n)) (0R-absorb-r (f 1)) ⟩
  0R +R (f ⁺ ⁺ ·' X') (suc n)
    ≡⟨ snd (+R-identity ((f ⁺ ⁺ ·' X') (suc n))) ⟩
  (f ⁺ ⁺ ·' X') (suc n)
    ≡⟨ refl ⟩
  (f 2 ⋆' 1s') n  +R (f ⁺ ⁺ ⁺ ·' X') n
    ≡⟨ cong (λ x → x n +R (f ⁺ ⁺ ⁺ ·' X') n) (⋆1s≡⟦⟧' (f 2)) ⟩
  ⟦ (f ⁺ ⁺) 0 ⟧' n  +R ((f ⁺ ⁺) ⁺ ·' X') n
    ≡⟨ sym (+'-compwise-n ⟦ (f ⁺ ⁺) 0 ⟧' ((f ⁺ ⁺) ⁺ ·' X') n) ⟩
  (⟦ (f ⁺ ⁺) 0 ⟧' +' ((f ⁺ ⁺) ⁺ ·' X')) n
    ≡⟨ ·'-X'-n (f ⁺ ⁺) n ⟩
  f (suc (suc n))
    ∎

·'-X' : ∀ f → ⟦ f 0 ⟧' +' (f ⁺) ·' X' ≡ f
·'-X' f i n = ·'-X'-n f n i

0s'-absorbL-n : ∀ f n → (0s' ·' f) n ≡ 0R
0s'-absorbL-n f 0 = 
  (0s' ·' f) 0
    ≡⟨ 0R-absorb-l (f 0) ⟩
  0R
    ∎
0s'-absorbL-n f (suc n) = 
  (0s' ·' f) (suc n) 
    ≡⟨ refl ⟩
  0R ·R f (suc n)  +R  (0s' ·' f) n
    ≡⟨ cong₂ _+R_ 
        (0R-absorb-l (f (suc n)))
        (0s'-absorbL-n f n)
    ⟩
  0R +R 0R
    ≡⟨ fst (+R-identity 0R) ⟩
  0R
    ∎

0s'-absorbR-n : ∀ f n → (f ·' 0s') n ≡ 0s' n
0s'-absorbR-n f 0 = 
  (f ·' 0s') 0
    ≡⟨ 0R-absorb-r (f 0) ⟩
  0R
    ∎
0s'-absorbR-n f (suc n) = 
  (f ·' 0s') (suc n) 
    ≡⟨ refl ⟩
  f 0 ·R 0R  +R  (f ⁺ ·' 0s') n
    ≡⟨ cong₂ _+R_ 
        (0R-absorb-r (f 0))
        (0s'-absorbR-n (f ⁺) n)
    ⟩
  0R +R 0R
    ≡⟨ snd (+R-identity 0R) ⟩
  0s' (suc n)
    ∎

0s'-absorbL : ∀ f → 0s' ·' f ≡ 0s'
0s'-absorbL f i n = 0s'-absorbL-n f n i

0s'-absorbR : ∀ f → f ·' 0s' ≡ 0s'
0s'-absorbR f i n = 0s'-absorbR-n f n i

⟦⟧'-·'-n : ∀ r x n → (⟦ r ⟧' ·' x) n ≡ (r ⋆' x) n
⟦⟧'-·'-n r x 0 = refl
⟦⟧'-·'-n r x (suc n) = 
  (⟦ r ⟧' ·' x) (suc n)
    ≡⟨ refl ⟩
  (r ⋆' x) (suc n) +R (0s' ·' x) n
    ≡⟨ cong ((r ⋆' x) (suc n) +R_) (0s'-absorbL-n x n) ⟩
  (r ⋆' x) (suc n) +R 0R
    ≡⟨ fst (+R-identity ((r ⋆' x) (suc n))) ⟩
  (r ⋆' x) (suc n)
    ∎

⟦⟧'-·' : ∀ r x → ⟦ r ⟧' ·' x ≡ r ⋆' x
⟦⟧'-·' r x i n = ⟦⟧'-·'-n r x n i

·'-⟦⟧'-n : ∀ x r n → (x ·' ⟦ r ⟧') n ≡ (r ⋆' x) n
·'-⟦⟧'-n x r 0 = ·R-comm (x 0) r
·'-⟦⟧'-n x r (suc n) =
  (x ·' ⟦ r ⟧') (suc n)
    ≡⟨ refl ⟩
  x 0 ·R 0R  +R  (x ⁺ ·'  ⟦ r ⟧') n
    ≡⟨ cong (_+R (x ⁺ ·'  ⟦ r ⟧') n) (0R-absorb-r (x 0)) ⟩ 
  0R  +R  (x ⁺ ·'  ⟦ r ⟧') n
    ≡⟨ snd (+R-identity ((x ⁺ ·'  ⟦ r ⟧') n)) ⟩ 
  (x ⁺ ·'  ⟦ r ⟧') n
    ≡⟨ ·'-⟦⟧'-n (x ⁺) r n ⟩ 
  (r ⋆' x ⁺) n
    ≡⟨ refl ⟩ 
  (r ⋆' x) (suc n)
    ∎

·'-⟦⟧' : ∀ x r → x ·' ⟦ r ⟧' ≡ r ⋆' x
·'-⟦⟧' x r i n = ·'-⟦⟧'-n x r n i

private
  lem1 : ∀ fg⁺ fh⁺ f⁺g f⁺h
      → (fg⁺ +R fh⁺) +R (f⁺g +R f⁺h) ≡ (fg⁺ +R f⁺g) +R (fh⁺ +R f⁺h)
  lem1 = solve R

·'‿+'-distrib-l-n : ∀ f g h n → (f ·' (g +' h)) n ≡ (f ·' g  +'  f ·' h) n
·'‿+'-distrib-l-n  f g h 0 =
  (f ·' (g +' h)) 0
    ≡⟨ refl ⟩
  f 0 ·R ((g +' h) 0) 
    ≡⟨ cong (f 0 ·R_) (+'-compwise-n g h 0) ⟩
  f 0 ·R (g 0 +R h 0) 
    ≡⟨ R-·Rdist+ (f 0) (g 0) (h 0) ⟩
  f 0 ·R g 0 +R f 0 ·R h 0
    ≡⟨ refl ⟩ 
  (f ·' g) 0 +R (f ·' h) 0
    ≡⟨ sym (+'-compwise-n (f ·' g ) (f ·' h) 0) ⟩ 
  (f ·' g  +'  f ·' h) 0
    ∎
·'‿+'-distrib-l-n f g h (suc n) = 
  (f ·' (g +' h)) (suc n) 
    ≡⟨ refl ⟩
  (f 0 ⋆' (g ⁺ +' h ⁺)) n  +R  (f ⁺ ·' (g +' h)) n
    ≡⟨ cong₂ _+R_
        (cong (λ k → k n) (⋆-rdist' (f 0) (g ⁺) (h ⁺)))
        (·'‿+'-distrib-l-n (f ⁺) g h n)
    ⟩
  (f 0 ⋆' g ⁺ +' f 0 ⋆' h ⁺) n  +R  (f ⁺ ·' g +' f ⁺ ·' h) n
    ≡⟨ cong₂ _+R_ 
        (+'-compwise-n (f 0 ⋆' g ⁺) (f 0 ⋆' h ⁺) n)
        (+'-compwise-n (f ⁺ ·' g) (f ⁺ ·' h) n)
      ⟩
  ((f 0 ⋆' g ⁺) n +R (f 0 ⋆' h ⁺) n)  +R  ((f ⁺ ·' g) n +R (f ⁺ ·' h) n)
    ≡⟨ lem1 ((f 0 ⋆' g ⁺) n) ((f 0 ⋆' h ⁺) n) ((f ⁺ ·' g) n) ((f ⁺ ·' h) n) ⟩
  ((f 0 ⋆' g ⁺) n +R (f ⁺ ·' g) n)  +R  ((f 0 ⋆' h ⁺) n +R (f ⁺ ·' h) n)
    ≡⟨ refl ⟩
  (f ·' g) (suc n)  +R  (f ·' h) (suc n)
    ≡⟨ sym (+'-compwise-n (f ·' g) (f ·' h) (suc n)) ⟩
  (f ·' g  +'  f ·' h) (suc n)
    ∎

·'‿+'-distrib-l : ∀ f g h → (f ·' (g +' h)) ≡ (f ·' g  +'  f ·' h)
·'‿+'-distrib-l f g h i n = ·'‿+'-distrib-l-n f g h n i

·'‿+'-distrib-r-n : ∀ f g h n → ((f +' g) ·' h) n ≡ (f ·' h  +'  g ·' h) n
·'‿+'-distrib-r-n  f g h 0 =
  ((f +' g) ·' h) 0
    ≡⟨ refl ⟩
  ((f +' g) 0) ·R h 0
    ≡⟨ cong (_·R h 0) (+'-compwise-n f g 0) ⟩
  (f 0 +R g 0) ·R h 0
    ≡⟨ R-·Ldist+ (f 0) (g 0) (h 0) ⟩
  f 0 ·R h 0 +R g 0 ·R h 0
    ≡⟨ refl ⟩ 
  (f ·' h) 0 +R (g ·' h) 0
    ≡⟨ sym (+'-compwise-n (f ·' h) (g ·' h) 0) ⟩ 
  (f ·' h  +'  g ·' h) 0
    ∎
·'‿+'-distrib-r-n f g h (suc n) = 
  ((f +' g) ·' h) (suc n) 
    ≡⟨ refl ⟩
  ((f +' g) 0 ⋆' h ⁺) n  +R  ((f +' g)⁺ ·' h) n
    ≡⟨ cong₂ _+R_
        (cong (λ k → k n) 
          (
            (f +' g) 0 ⋆' h ⁺
              ≡⟨ cong (_⋆' (h ⁺)) (+'-compwise-n f g 0 ) ⟩
            (f 0 +R g 0) ⋆' h ⁺
              ≡⟨ ⋆-ldist' (f 0) (g 0) (h ⁺) ⟩
            (f 0 ⋆' h ⁺ +' g 0 ⋆' h ⁺)
              ∎
          )
        )
        (
          ((f +' g)⁺ ·' h) n
            ≡⟨ refl ⟩
          ((f ⁺ +' g ⁺) ·' h) n
            ≡⟨ ·'‿+'-distrib-r-n (f ⁺) (g ⁺) h n ⟩
          (f ⁺ ·' h  +' g ⁺ ·' h) n
            ∎
        )
    ⟩
  (f 0 ⋆' h ⁺ +' g 0 ⋆' h ⁺) n  +R  (f ⁺ ·' h +' g ⁺ ·' h) n
    ≡⟨ cong₂ _+R_ 
        (+'-compwise-n (f 0 ⋆' h ⁺) (g 0 ⋆' h ⁺) n)
        (+'-compwise-n (f ⁺ ·' h) (g ⁺ ·' h) n)
      ⟩
  ((f 0 ⋆' h ⁺) n +R (g 0 ⋆' h ⁺) n)  +R  ((f ⁺ ·' h) n +R (g ⁺ ·' h) n)
    ≡⟨ lem1 ((f 0 ⋆' h ⁺) n) ((g 0 ⋆' h ⁺) n) ((f ⁺ ·' h) n) ((g ⁺ ·' h) n) ⟩
  ((f 0 ⋆' h ⁺) n +R (f ⁺ ·' h) n)  +R  ((g 0 ⋆' h ⁺) n +R (g ⁺ ·' h) n)
    ≡⟨ refl ⟩
  (f ·' h) (suc n)  +R  (g ·' h) (suc n)
    ≡⟨ sym (+'-compwise-n (f ·' h) (g ·' h) (suc n)) ⟩
  (f ·' h  +'  g ·' h) (suc n)
    ∎

·'‿+'-distrib-r : ∀ f g h → ((f +' g) ·' h) ≡ (f ·' h  +'  g ·' h)
·'‿+'-distrib-r f g h i n = ·'‿+'-distrib-r-n f g h n i

·'-assoc-n : ∀ f g h n → (f ·' (g ·' h)) n ≡ ((f ·' g) ·' h) n
·'-assoc-n f g h 0 = ·R-assoc (f 0) (g 0) (h 0)
·'-assoc-n f g h (suc n) = 
  (f ·' (g ·' h)) (suc n)
    ≡⟨ refl ⟩
  (f 0 ⋆' (g ·' h)⁺) n +R (f ⁺ ·' (g ·' h)) n
    ≡⟨ cong (λ x → (f 0 ⋆' x) n +R (f ⁺ ·' (g ·' h)) n) (·'‿⁺ g h) ⟩
  (f 0 ⋆' ((g 0 ⋆' h ⁺) +' (g ⁺ ·' h))) n +R (f ⁺ ·' (g ·' h)) n
    ≡⟨ cong (λ k → k n +R (f ⁺ ·' (g ·' h)) n) 
        (⋆-rdist' (f 0) (g 0 ⋆' h ⁺) (g ⁺ ·' h))
    ⟩
  (f 0 ⋆' (g 0 ⋆' h ⁺) +' f 0 ⋆' (g ⁺ ·' h)) n +R (f ⁺ ·' (g ·' h)) n
    ≡⟨ cong (_+R (f ⁺ ·' (g ·' h)) n)  
        (+'-compwise-n (f 0 ⋆' (g 0 ⋆' h ⁺)) (f 0 ⋆' (g ⁺ ·' h)) n)
    ⟩
  ((f 0 ⋆' (g 0 ⋆' h ⁺)) n +R (f 0 ⋆' (g ⁺ ·' h)) n) +R (f ⁺ ·' (g ·' h)) n
    ≡⟨ sym (+R-assoc ((f 0 ⋆' (g 0 ⋆' h ⁺)) n) 
                     ((f 0 ⋆' (g ⁺ ·' h)) n) 
                     ((f ⁺ ·' (g ·' h)) n)) 
    ⟩
  (f 0 ⋆' (g 0 ⋆' h ⁺)) n +R ((f 0 ⋆' (g ⁺ ·' h)) n  +R  (f ⁺ ·' (g ·' h)) n)
    ≡⟨ cong ((f 0 ⋆' (g 0 ⋆' h ⁺)) n +R_)
        ( (f 0 ⋆' (g ⁺ ·' h)) n  +R  (f ⁺ ·' (g ·' h)) n
            ≡⟨
              cong₂ _+R_
                ( 
                  (f 0 ⋆' (g ⁺ ·' h)) n
                    ≡⟨ 
                      cong (λ k → k n)
                      (sym (⟦⟧'-·' (f 0) (g ⁺ ·' h)))
                    ⟩
                  (⟦ f 0 ⟧' ·' (g ⁺ ·' h)) n
                    ≡⟨ ·'-assoc-n ⟦ f 0 ⟧' (g ⁺) h n ⟩
                  ((⟦ f 0 ⟧' ·' g ⁺) ·' h) n
                    ∎
                )
                (·'-assoc-n (f ⁺) g h n)
            ⟩
          ((⟦ f 0 ⟧' ·' g ⁺) ·' h) n  +R  ((f ⁺ ·' g) ·' h) n
            ≡⟨ sym (+'-compwise-n ((⟦ f 0 ⟧' ·' g ⁺) ·' h) ((f ⁺ ·' g) ·' h) n)  ⟩
          ((⟦ f 0 ⟧' ·' g ⁺) ·' h  +'  (f ⁺ ·' g) ·' h) n
            ≡⟨ cong (λ k → k n) 
              (
                (⟦ f 0 ⟧' ·' g ⁺) ·' h  +'  (f ⁺ ·' g) ·' h
                  ≡⟨ sym (·'‿+'-distrib-r (⟦ f 0 ⟧' ·' g ⁺) (f ⁺ ·' g) h ) ⟩
                (⟦ f 0 ⟧' ·' g ⁺  +'  (f ⁺ ·' g)) ·' h
                  ≡⟨ cong (λ x → (x  +'  (f ⁺ ·' g)) ·' h) 
                      (⟦⟧'-·' (f 0) (g ⁺) )
                  ⟩
                (f 0 ⋆' g ⁺  +'  f ⁺ ·' g) ·' h
                  ≡[ i ]⟨ ·'‿⁺ f g (~ i) ·' h ⟩
                (f ·' g)⁺ ·' h
                  ∎
              )
            ⟩
          ((f ·' g)⁺ ·' h) n
            ∎
        )
    ⟩
  (f 0 ⋆' (g 0 ⋆' h ⁺)) n +R ((f ·' g)⁺ ·' h) n
    ≡⟨ cong (λ k → k n +R ((f ·' g)⁺ ·' h) n) (sym (⋆-assoc' (f 0) (g 0) (h ⁺))) ⟩
  ((f 0 ·R g 0) ⋆' h ⁺) n +R ((f ·' g)⁺ ·' h) n
    ≡⟨ refl ⟩
  ((f ·' g) ·' h) (suc n)
    ∎

·'-assoc : ∀ f g h → f ·' (g ·' h) ≡ (f ·' g) ·' h
·'-assoc f g h i n = ·'-assoc-n f g h n i

·'‿⁺-unfold : ∀ f g → (f ·' g) ⁺ ≡ f 0 ⋆' g ⁺ +' (f ⁺ ·' g ⁺) ·' X' +' g 0 ⋆' f ⁺
·'‿⁺-unfold f g = 
  (f ·' g)⁺
    ≡⟨ ·'‿⁺ f g ⟩
  f 0 ⋆' g ⁺ +' f ⁺ ·' g
    ≡⟨ cong (λ h → f 0 ⋆' g ⁺ +' f ⁺ ·' h) (sym (·'-X' g)) ⟩
  f 0 ⋆' g ⁺ +' f ⁺ ·' (⟦ g 0 ⟧' +' (g ⁺) ·' X')
    ≡⟨ cong (f 0 ⋆' g ⁺ +'_) (·'‿+'-distrib-l (f ⁺) ⟦ g 0 ⟧' ((g ⁺) ·' X') ) ⟩
  f 0 ⋆' g ⁺ +' (f ⁺ ·' ⟦ g 0 ⟧' +' f ⁺ ·' ((g ⁺) ·' X'))
    ≡⟨ cong (f 0 ⋆' g ⁺ +'_) 
      (cong₂ _+'_
        (·'-⟦⟧' (f ⁺) (g 0))
        (·'-assoc (f ⁺) (g ⁺) X')
      )
    ⟩
  f 0 ⋆' g ⁺ +' (g 0 ⋆' f ⁺ +' (f ⁺ ·' g ⁺) ·' X')
    ≡⟨ cong (f 0 ⋆' g ⁺ +'_) (+'-comm (g 0 ⋆' f ⁺) ((f ⁺ ·' g ⁺) ·' X')) ⟩
  f 0 ⋆' g ⁺ +' ((f ⁺ ·' g ⁺) ·' X' +' g 0 ⋆' f ⁺)
    ≡⟨ +'-assoc (f 0 ⋆' g ⁺) ((f ⁺ ·' g ⁺) ·' X') (g 0 ⋆' f ⁺) ⟩
  f 0 ⋆' g ⁺ +' (f ⁺ ·' g ⁺) ·' X' +' g 0 ⋆' f ⁺
    ∎

+'-+'-+'-compwise : ∀ f g h n →
  (f +' g +' h) n ≡ f n +R g n +R h n
+'-+'-+'-compwise f g h n = 
  (f +' g +' h) n 
    ≡⟨ +'-compwise-n (f +' g) h n ⟩
  (f +' g ) n +R h n 
    ≡⟨ cong (_+R h n) (+'-compwise-n f g n) ⟩
  f n +R g n +R h n 
    ∎

·'-comm-X'-n : ∀ f n → (f ·' X') n ≡ (X' ·' f) n
·'-comm-X'-n f 0 = ·R-comm (f 0) 0R
·'-comm-X'-n f 1 =
  (f ·' X') 1
    ≡⟨ refl ⟩
  f 0 ·R 1R +R f 1 ·R 0R
    ≡⟨ cong₂ _+R_ 
        (fst (·R-identity (f 0)))
        (0R-absorb-r (f 1))
    ⟩
  f 0 +R 0R
    ≡⟨ fst (+R-identity (f 0)) ⟩
  f 0
    ≡⟨ sym (snd (+R-identity (f 0))) ⟩
  0R +R f 0
    ≡⟨ sym (cong₂ _+R_ 
        (0R-absorb-l (f 1))
        (snd (·R-identity (f 0))))
    ⟩
  0R ·R f 1 +R 1R ·R f 0
    ≡⟨ refl ⟩
  (X' ·' f) 1
    ∎
·'-comm-X'-n f (suc (suc n)) =
  (f ·' X') (suc (suc n))
    ≡⟨ refl ⟩
  (f 0 ⋆' 1s') (suc n) +R (f ⁺ ·' X') (suc n)
    ≡⟨ refl ⟩
  (f 0 ·R 0R) +R ((f 1 ⋆' 1s') n  +R  (f ⁺ ⁺ ·' X') n)
    ≡⟨ cong 
      (_+R ((f 1 ⋆' 1s') n  +R  (f ⁺ ⁺ ·' X') n))
      (0R-absorb-r (f 0))
    ⟩
  0R +R ((f 1 ⋆' 1s') n  +R  (f ⁺ ⁺ ·' X') n)
    ≡⟨ snd (+R-identity ((f 1 ⋆' 1s') n  +R  (f ⁺ ⁺ ·' X') n)) ⟩ 
  (f 1 ⋆' 1s') n  +R  (f ⁺ ⁺ ·' X') n
    ≡⟨ cong (_+R  ((f ⁺) ⁺ ·' X') n) 
        (λ i → ⋆1s≡⟦⟧' (f 1) i n)
    ⟩
  ⟦ (f ⁺) 0 ⟧' n  +R  ((f ⁺) ⁺ ·' X') n
    ≡⟨ sym (+'-compwise-n ⟦ (f ⁺) 0 ⟧' ((f ⁺) ⁺ ·' X') n) ⟩
  (⟦ (f ⁺) 0 ⟧' +' (f ⁺) ⁺ ·' X') n
    ≡⟨ ·'-X'-n (f ⁺) n ⟩
  (f ⁺) n
    ≡⟨ sym (fst (+R-identity (f (suc n)))) ⟩
  f (suc n) +R 0R
    ≡⟨ cong₂ _+R_
      (sym (snd (·R-identity (f (suc n)))))
      (sym (0s'-absorbL-n f n))
    ⟩
  1R ·R (f (suc n)) +R (0s' ·' f) n
    ≡⟨ refl ⟩
  (1s' ·' f) (suc n)
    ≡⟨ sym (snd (+R-identity ((1s' ·' f) (suc n)))) ⟩
  0R +R (1s' ·' f) (suc n)
    ≡⟨ cong (_+R (1s' ·' f) (suc n))
      (sym (0R-absorb-l (f (suc (suc n)))))
    ⟩
  0R ·R (f (suc (suc n))) +R (1s' ·' f) (suc n)
    ≡⟨ refl ⟩
  (X' ·' f) (suc (suc n))
    ∎

·'-comm-X' : ∀ f → f ·' X' ≡ X' ·' f
·'-comm-X' f i n = ·'-comm-X'-n f n i

·'-identityˡ-n : ∀ f n → (1s' ·' f) n ≡ f n
·'-identityˡ-n f 0 = snd (·R-identity (f 0))
·'-identityˡ-n f (suc n) = 
  (1s' ·' f) (suc n) 
    ≡⟨ refl ⟩
  1R ·R (f (suc n))  +R  (0s' ·' f) n
    ≡⟨ cong₂ _+R_ (snd (·R-identity (f (suc n)))) (0s'-absorbL-n f n)  ⟩
  f (suc n) +R  0R
    ≡⟨ fst (+R-identity (f (suc n))) ⟩
  f (suc n)
    ∎

·'-identityˡ : ∀ f → 1s' ·' f ≡ f
·'-identityˡ f i n = ·'-identityˡ-n f n i

private
  exch : ∀ x y z → x +R y +R z ≡ z +R y +R x
  exch = solve R

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
    ≡⟨ cong (λ  k →  k n) (·'‿⁺-unfold f g) ⟩
  (f 0 ⋆' g ⁺ +' (f ⁺ ·' g ⁺) ·' X' +' g 0 ⋆' f ⁺) n
    ≡⟨ +'-+'-+'-compwise (f 0 ⋆' g ⁺) ((f ⁺ ·' g ⁺) ·' X') (g 0 ⋆' f ⁺) n ⟩
  (f 0 ⋆' g ⁺) n +R ((f ⁺ ·' g ⁺) ·' X') n +R (g 0 ⋆' f ⁺) n
    ≡⟨ cong 
        (λ x → (f 0 ⋆' g ⁺) n +R x +R (g 0 ⋆' f ⁺) n) 
        (
          ((f ⁺ ·' g ⁺) ·' X') n
            ≡⟨ ·'-comm-n (f ⁺ ·' g ⁺) X' n ⟩
          (X' ·' (f ⁺ ·' g ⁺)) n
            ≡⟨ ·'-assoc-n X' (f ⁺) (g ⁺) n ⟩
          ((X' ·' f ⁺) ·' g ⁺) n
            ≡⟨ cong (λ h → (h ·' g ⁺) n) (sym (·'-comm-X' (f ⁺))) ⟩
          ((f ⁺ ·' X') ·' g ⁺) n
            ≡⟨ ·'-comm-n (f ⁺ ·' X') (g ⁺) n ⟩
          (g ⁺ ·' (f ⁺ ·' X')) n
            ≡⟨ ·'-assoc-n (g ⁺) (f ⁺) X' n ⟩
          ((g ⁺ ·' f ⁺) ·' X') n
            ∎
        )
    ⟩
  (f 0 ⋆' g ⁺) n +R ((g ⁺ ·' f ⁺) ·' X') n +R (g 0 ⋆' f ⁺) n
    ≡⟨ exch ((f 0 ⋆' g ⁺) n) (((g ⁺ ·' f ⁺) ·' X') n) ((g 0 ⋆' f ⁺) n) ⟩
  (g 0 ⋆' f ⁺) n +R ((g ⁺ ·' f ⁺) ·' X') n +R (f 0 ⋆' g ⁺) n
    ≡⟨ sym (+'-+'-+'-compwise (g 0 ⋆' f ⁺) ((g ⁺ ·' f ⁺) ·' X') (f 0 ⋆' g ⁺) n ) ⟩
  (g 0 ⋆' f ⁺ +' (g ⁺ ·' f ⁺) ·' X' +' f 0 ⋆' g ⁺) n
    ≡⟨ cong (λ  k →  k n) (sym (·'‿⁺-unfold g f)) ⟩
  (g ·' f) (suc n)
    ∎

·'-comm : ∀ f g → f ·' g ≡ g ·' f
·'-comm f g i n = ·'-comm-n f g n i

·'-identityʳ : ∀ f → f ·' 1s' ≡ f
·'-identityʳ f = ·'-comm f 1s' ∙ ·'-identityˡ f


·-assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
·-assoc = 
  transport 
    (λ i → (x y z : Series≡ℕ→R (~ i)) → 
      mulp i x (mulp i y z) ≡ mulp i (mulp i x y) z
    )
    ·'-assoc

·-IsSemigroup : IsSemigroup _·_
·-IsSemigroup = issemigroup PowerSeries-isSet ·-assoc

·-identityʳ : ∀ x → x · 1s ≡ x
·-identityʳ = 
  transport 
    (λ i → (x : Series≡ℕ→R (~ i)) → 
      let 1sᵢ = onep i
          _·ᵢ_ = mulp i
      in x ·ᵢ 1sᵢ ≡ x
    )
    ·'-identityʳ

·-identityˡ : ∀ x → 1s · x ≡ x
·-identityˡ = 
  transport 
    (λ i → (x : Series≡ℕ→R (~ i)) → 
      let 1sᵢ = onep i
          _·ᵢ_ = mulp i
      in 1sᵢ ·ᵢ x ≡ x
    )
    ·'-identityˡ

·-identity : ∀ x → (x · 1s ≡ x) × (1s · x ≡ x)
·-identity x = (·-identityʳ x , ·-identityˡ x)

·-IsMonoid : IsMonoid 1s _·_
·-IsMonoid = ismonoid ·-IsSemigroup ·-identity

·-comm : ∀ x y → x · y ≡ y · x
·-comm = 
  transport 
    (λ i → (x y : Series≡ℕ→R (~ i)) → 
      let _·ᵢ_ = mulp i
      in x ·ᵢ y ≡ y ·ᵢ x
    )
    ·'-comm

distˡ : ∀ x y z → x · (y + z) ≡ x · y  +  x · z
distˡ =
  transport
    (λ i → (x y z : Series≡ℕ→R (~ i)) → 
      let _·ᵢ_ = mulp i
          _+ᵢ_ = addp i
      in x ·ᵢ (y +ᵢ z) ≡ (x ·ᵢ y) +ᵢ (x ·ᵢ z)
    )
    ·'‿+'-distrib-l

distʳ : ∀ x y z → (x + y) · z ≡ x · z  +  y · z
distʳ =
  transport
    (λ i → (x y z : Series≡ℕ→R (~ i)) → 
      let _·ᵢ_ = mulp i
          _+ᵢ_ = addp i
      in (x +ᵢ y) ·ᵢ z ≡ (x ·ᵢ z)  +ᵢ  (y ·ᵢ z)
    )
    ·'‿+'-distrib-r

+-·-distrib : ∀ x y z → 
  (x · (y + z) ≡ x · y  +  x · z) × ((x + y) · z ≡ x · z  +  y · z)
+-·-distrib x y z = (distˡ x y z , distʳ x y z)

Series-IsRing : IsRing 0s 1s  _+_ _·_ -_
Series-IsRing = isring +-isAbGroup ·-IsMonoid +-·-distrib

Series-IsCommRing : IsCommRing 0s 1s _+_ _·_ -_
Series-IsCommRing = iscommring Series-IsRing ·-comm

Series-CommRingStr : CommRingStr PowerSeries
Series-CommRingStr = commringstr 0s 1s _+_ _·_ -_ Series-IsCommRing

Series-CommRing : CommRing _
Series-CommRing = (_ , Series-CommRingStr)

infix  8 -'_
-'_ : (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩)
-'_ = transport (λ i → Series≡ℕ→R i → Series≡ℕ→R i) -_

negp⁻ : PathP (λ i → Series≡ℕ→R i → Series≡ℕ→R i) -_ -'_
negp⁻ =
  transport-filler (λ i → Series≡ℕ→R i → Series≡ℕ→R i) -_

negp : PathP (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) -'_ -_
negp i = negp⁻ (~ i)

ℕ→R-IsCommRing : IsCommRing 0s' 1s' _+'_ _·'_ -'_
ℕ→R-IsCommRing =
  transport
    (λ i → IsCommRing (zerop (~ i)) (onep (~ i)) (addp (~ i)) (mulp (~ i)) (negp (~ i)) )
    Series-IsCommRing

ℕ→R-CommRingStr : CommRingStr (ℕ → ⟨ R ⟩)
ℕ→R-CommRingStr = 
  commringstr 0s' 1s' _+'_ _·'_ -'_ ℕ→R-IsCommRing

ℕ→R-CommRing : CommRing _
ℕ→R-CommRing = (_ , ℕ→R-CommRingStr)

X'-shift-n : ∀ f n → (f ·' X') (suc n) ≡ f n
X'-shift-n f 0 =
  f 0 ·R 1R +R f 1 ·R 0R 
    ≡⟨ cong₂ _+R_ (fst (·R-identity (f 0))) (0R-absorb-r (f 1)) ⟩ 
  f 0  +R 0R
    ≡⟨ fst (+R-identity (f 0)) ⟩ 
  f 0
  ∎
X'-shift-n f (suc n) =
  (f ·' X') (suc (suc n)) 
    ≡⟨ refl ⟩
  f 0 ·R 0R +R (f ⁺ ·' X') (suc n)
    ≡⟨ cong₂ _+R_ 
        (0R-absorb-r (f 0))
        (X'-shift-n (f ⁺) n)
    ⟩
  0R +R (f ⁺) n
    ≡⟨ snd (+R-identity (f (suc n))) ⟩
  f (suc n)
    ∎

·-head : ∀ f g → head (f · g) ≡ head f ·R head g
·-head f g =
  head (f · g)
    ≡⟨ cong head (liftℕ→ROp₂-unfold _·'_ f g) ⟩
  head (ℕ→R⟶Series (Series⟶ℕ→R f ·' Series⟶ℕ→R g))
    ≡⟨ refl ⟩
  (Series⟶ℕ→R f) 0 ·R (Series⟶ℕ→R g) 0
    ≡⟨ refl ⟩
  head f ·R head g
    ∎

·'-tail : ∀ f g → (f ·' g)⁺ ≡ f 0 ⋆' g ⁺ +' f ⁺ ·' g
·'-tail f g = sym (+'-compwise (f 0 ⋆' g ⁺) (f ⁺ ·' g))

·-tail : ∀ f g → tail (f · g) ≡ head f ⋆ tail g + tail f · g
·-tail =
  transport
    (λ i → (x y : Series≡ℕ→R (~ i)) → 
      let tailᵢ = tailp i
          headᵢ = headp i
          _·ᵢ_ = mulp i
          _+ᵢ_ = addp i
          _⋆ᵢ_ = scalarp i
      in tailᵢ (x ·ᵢ y) ≡ (headᵢ x ⋆ᵢ tailᵢ y) +ᵢ (tailᵢ x ·ᵢ y)
    )
    ·'-tail

·-unfold : ∀ f g → (f · g) ≡ (head f ·R head g) ∷ (head f ⋆ tail g + tail f · g)
head (·-unfold f g i) = ·-head f g i
tail (·-unfold f g i) = ·-tail f g i

·-tail-symmetric : ∀ f g → 
  tail (f · g) ≡ head f ⋆ tail g + (tail f · tail g) · X + head g ⋆ tail f
·-tail-symmetric =
  transport
    (λ i → (f g : Series≡ℕ→R (~ i)) → 
      let tailᵢ = tailp i
          headᵢ = headp i
          Xᵢ = Xp i
          _·ᵢ_ = mulp i
          _+ᵢ_ = addp i
          _⋆ᵢ_ = scalarp i
      in tailᵢ (f ·ᵢ g) ≡
        ((headᵢ f ⋆ᵢ tailᵢ g) +ᵢ ((tailᵢ f ·ᵢ tailᵢ g) ·ᵢ Xᵢ)) 
          +ᵢ (headᵢ g ⋆ᵢ tailᵢ f)
    )
    ·'‿⁺-unfold

·-unfold-symmetric : ∀ f g → 
  (f · g) 
    ≡ (head f ·R head g) 
        ∷ (head f ⋆ tail g + (tail f · tail g) · X + head g ⋆ tail f)
head (·-unfold-symmetric f g i) = ·-head f g i
tail (·-unfold-symmetric f g i) = ·-tail-symmetric f g i

isolate-constant : ∀ f → ⟦ head f ⟧ + tail f · X ≡ f
isolate-constant = 
  transport
    (λ i → (f : Series≡ℕ→R (~ i)) →
      addp i (⟦ headp i f ⟧p i) (mulp i (tailp i f) (Xp i)) ≡ f
    )
    ·'-X'

⟦r⟧·x≡r⋆x : ∀ r x → ⟦ r ⟧ · x ≡ r ⋆ x
⟦r⟧·x≡r⋆x = 
  transport
    (λ i → (r : ⟨ R ⟩) (x : Series≡ℕ→R (~ i)) →
      mulp i (⟦ r ⟧p i) x ≡ scalarp i r x
    )
  ⟦⟧'-·'

f·g≡f₀g+tailf·g·X : ∀ f g → f · g ≡ head f ⋆ g + tail f · g · X
f·g≡f₀g+tailf·g·X f g =
  f · g
    ≡⟨ cong (_· g) (sym (isolate-constant f)) ⟩
  (⟦ head f ⟧ + tail f · X) · g
    ≡⟨ distʳ ⟦ head f ⟧ (tail f · X) g ⟩
  ⟦ head f ⟧ · g + (tail f · X) · g
    ≡⟨ cong₂ _+_ (⟦r⟧·x≡r⋆x (head f) g)(
      (tail f · X) · g
        ≡⟨ sym (·-assoc (tail f) X g ) ⟩
      tail f · (X · g)
        ≡⟨ cong (tail f ·_) (·-comm _ _) ⟩
      tail f · (g · X)
        ≡⟨ ·-assoc (tail f) g X ⟩
      (tail f · g) · X
        ∎
    )⟩
  head f ⋆ g + tail f · g · X
    ∎

open Sum (CommRing→Ring R)
open import Cubical.Data.FinData

toℕWeakenFin : ∀{n : ℕ} → ∀ (k : Fin n) → toℕ (weakenFin k) ≡ toℕ k
toℕWeakenFin zero = refl
toℕWeakenFin (suc k) =
  toℕ (weakenFin (suc k))
    ≡⟨ refl ⟩
  suc (toℕ (weakenFin k))
    ≡⟨ cong suc (toℕWeakenFin k) ⟩
  suc (toℕ k)
    ∎

n∸n≡0 : ∀ n → n -ℕ n ≡ 0
n∸n≡0 n = ∸-cancelʳ 0 0 n

open import Cubical.Data.Nat.Order

suc∸Fin : ∀ {n} (i : Fin (suc n)) → suc (n -ℕ toℕ i) ≡ suc n -ℕ toℕ i
suc∸Fin i = ≤-∸-suc i≤n
  where
    i<suc-n = toℕ<n i
    i≤n = pred-≤-pred i<suc-n

-- | Explicit coefficient formula.
·-explicit : ∀ f g n →  (f · g) [ n ] ≡ ∑ (λ(i : Fin (suc n)) → f [ n -ℕ toℕ i ] ·R g [ toℕ i ])
·-explicit f g 0 = 
  (f · g) [ 0 ]
    ≡⟨ ·-head f g ⟩
  head f ·R head g
    ≡⟨ sym (fst (+R-identity (head f ·R head g))) ⟩
  head f ·R head g +R 0R
    ∎
·-explicit f g (suc n) =
  (f · g) [ suc n ]
    ≡⟨ refl ⟩
  (tail (f · g)) [ n ]
    ≡⟨ cong _[ n ] (·-tail f g) ⟩
  (f [ 0 ] ⋆ tail g + tail f · g) [ n ]
    ≡⟨ index-additive-n (f [ 0 ] ⋆ tail g) (tail f · g) n ⟩
  (f [ 0 ] ⋆ tail g) [ n ] +R (tail f · g) [ n ]
    ≡⟨ +R-comm ((f [ 0 ] ⋆ tail g) [ n ]) _ ⟩
  (tail f · g) [ n ] +R (f [ 0 ] ⋆ tail g) [ n ]
    ≡⟨ cong₂ _+R_ (·-explicit (tail f) g n) (⋆-[] (f [ 0 ]) (tail g) n) ⟩
  (∑ (λ(i : Fin (suc n)) → f [ suc (n -ℕ toℕ i) ] ·R g [ toℕ i ])) 
    +R f [ 0 ] ·R (g [ suc n ])
    ≡⟨ cong₂ _+R_
        (cong ∑ (funExt (λ (k : Fin (suc n)) → 
          (cong (λ z → f [ z ] ·R g [ toℕ k ]) (suc∸Fin k) ∙
            cong (λ z → f [ suc n -ℕ z ] ·R g [ z ])
            (sym (toℕWeakenFin k))
          )
        )))
        (cong (λ z → f [ z ] ·R g [ suc n ]) (sym (n∸n≡0 (suc n))) 
          ∙ cong (λ z → f [ suc n -ℕ z ] ·R g [ z ]) (sym (toFromId (suc n)))
        )
    ⟩
  (∑ (λ(i : Fin (suc n)) → f [ suc n -ℕ toℕ (weakenFin i) ] ·R g [ toℕ (weakenFin i) ]))
    +R (f [ suc n -ℕ toℕ (fromℕ (suc n)) ] ·R g [ toℕ (fromℕ (suc n)) ]) 
    ≡⟨ sym (∑Last (λ(i : Fin (suc (suc n))) → f [ suc n -ℕ toℕ i ] ·R g [ toℕ i ])) ⟩
  (∑ (λ(i : Fin (suc (suc n))) → f [ suc n -ℕ toℕ i ] ·R g [ toℕ i ]))
    ∎

·'-explicit : ∀ f g n →  (f ·' g) n ≡ 
  ∑ (λ(i : Fin (suc n)) → f (n -ℕ toℕ i) ·R g (toℕ i))
·'-explicit =
  transport
  (λ i → 
    (f g : Series≡ℕ→R i) →
    (n : ℕ) →
    let _[_]ᵢ = []p (~ i)
    in mulp (~ i) f g [ n ]ᵢ ≡
        ∑ (λ(k : Fin (suc n)) → (f [ n -ℕ toℕ k ]ᵢ) ·R (g [ toℕ k ]ᵢ))
  )
  ·-explicit
