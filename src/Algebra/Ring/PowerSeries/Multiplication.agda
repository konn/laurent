{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.Ring.PowerSeries.Multiplication {ℓ} (R : CommRing ℓ) where
open import Cubical.Algebra.Ring
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
open import Cubical.Data.Nat
  using ( ℕ ; suc )
  renaming (_+_ to _+ℕ_; _·_ to _·ℕ_)
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
  )

infixl 8 _·ℕ→_ _·'_
_·ℕ→_ : (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩) → (ℕ → ⟨ R ⟩)
_·ℕ→_ f g 0 = f 0 ·R g 0
_·ℕ→_ f g (suc n) = 
  (f ·ℕ→ g ⁺) n +R (f ⁺ ·ℕ→ g) n

_·'_ = _·ℕ→_

·ℕ→-curry : ∀ f g n → (f ·ℕ→ g) (suc n) ≡ (f ·ℕ→ g ⁺ +' f ⁺ ·ℕ→ g) n
·ℕ→-curry f g n =
    (f ·ℕ→ g) (suc n) 
  ≡⟨ sym (+'-compwise-n (f ·ℕ→ g ⁺) (f ⁺ ·ℕ→ g) n) ⟩ 
    (f ·ℕ→ g ⁺ +' f ⁺ ·ℕ→ g) n
  ∎

·ℕ→‿⁺ : ∀ f g → (f ·ℕ→ g)⁺ ≡ (f ·ℕ→ g ⁺ +' f ⁺ ·ℕ→ g)
·ℕ→‿⁺ f g i n = ·ℕ→-curry f g n i

infixl 8 _·_
_·_ : PowerSeries → PowerSeries → PowerSeries
_·_ = liftℕ→ROp₂ _·ℕ→_

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
  (f ·' (g +' h)⁺) n  +R  (f ⁺ ·' (g +' h)) n
    ≡⟨ refl ⟩
  (f ·' (g ⁺ +' h ⁺)) n  +R  (f ⁺ ·' (g +' h)) n
    ≡⟨ cong₂ _+R_
        (·'‿+'-distrib-l-n f (g ⁺) (h ⁺) n)
        (·'‿+'-distrib-l-n (f ⁺) g h n)
    ⟩
  (f ·' g ⁺ +' f ·' h ⁺) n  +R  (f ⁺ ·' g +' f ⁺ ·' h) n
    ≡⟨ cong₂ _+R_ 
        (+'-compwise-n (f ·' g ⁺) (f ·' h ⁺) n)
        (+'-compwise-n (f ⁺ ·' g) (f ⁺ ·' h) n)
      ⟩
  ((f ·' g ⁺) n +R (f ·' h ⁺) n)  +R  ((f ⁺ ·' g) n +R (f ⁺ ·' h) n)
    ≡⟨ lem1 ((f ·' g ⁺) n) ((f ·' h ⁺) n) ((f ⁺ ·' g) n) ((f ⁺ ·' h) n) ⟩
  ((f ·' g ⁺) n +R (f ⁺ ·' g) n)  +R  ((f ·' h ⁺) n +R (f ⁺ ·' h) n)
    ≡⟨ refl ⟩
  (f ·' g) (suc n)  +R  (f ·' h) (suc n)
    ≡⟨ sym (+'-compwise-n (f ·' g) (f ·' h) (suc n)) ⟩
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
        (+'-compwise-n (f ·' (g ·' h ⁺)) (f ·' (g ⁺ ·' h)) n)
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
            ≡⟨ sym (+'-compwise-n ((f ·' g ⁺) ·' h) ((f ⁺ ·' g) ·' h) n) ⟩
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
1s' 0 = 1R
1s' (suc n) = 0R

0s' : ℕ → ⟨ R ⟩
0s' n = 0R

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

Series⟶ℕ→R‿·' : 
  ∀ f g → Series⟶ℕ→R f ·' Series⟶ℕ→R g ≡ Series⟶ℕ→R (f · g)
Series⟶ℕ→R‿·' f g = 
  Series⟶ℕ→R f ·' Series⟶ℕ→R g 
    ≡⟨ sym (Ser-Nat-sect (Series⟶ℕ→R f ·' Series⟶ℕ→R g)) ⟩
  Series⟶ℕ→R (ℕ→R⟶Series (Series⟶ℕ→R f ·' Series⟶ℕ→R g))
    ≡⟨ cong Series⟶ℕ→R (sym (liftℕ→ROp₂-unfold _·'_ f g)) ⟩
  Series⟶ℕ→R (f · g)
    ∎

·-tail : ∀ f g → tail (f · g) ≡ f · tail g + tail f · g
·-tail f g =
  tail (f · g) 
    ≡⟨ cong tail (liftℕ→ROp₂-unfold _·'_ f g ) ⟩
  tail (ℕ→R⟶Series (Series⟶ℕ→R f ·' Series⟶ℕ→R  g))
    ≡⟨ refl ⟩
  ℕ→R⟶Series ((Series⟶ℕ→R f ·' Series⟶ℕ→R  g) ⁺)
    ≡⟨  cong ℕ→R⟶Series 
      ( (Series⟶ℕ→R f ·' Series⟶ℕ→R  g) ⁺ 
          ≡⟨ ·ℕ→‿⁺ (Series⟶ℕ→R f) (Series⟶ℕ→R g) ⟩
        Series⟶ℕ→R f ·' (Series⟶ℕ→R  g) ⁺  +'  (Series⟶ℕ→R f)⁺ ·' Series⟶ℕ→R g
          ≡⟨ refl ⟩
        Series⟶ℕ→R f ·' Series⟶ℕ→R (tail g)  +' Series⟶ℕ→R (tail f) ·' Series⟶ℕ→R g
          ≡⟨ cong₂ _+'_ 
              (Series⟶ℕ→R‿·' f (tail g)) 
              (Series⟶ℕ→R‿·' (tail f) g)
          ⟩
        Series⟶ℕ→R (f · tail g) +' Series⟶ℕ→R (tail f · g)
          ∎
      )
    ⟩
  ℕ→R⟶Series (Series⟶ℕ→R (f · tail g) +' Series⟶ℕ→R (tail f · g))
    ≡⟨ sym (liftℕ→ROp₂-unfold _+'_ (f · tail g) (tail f · g)) ⟩
  liftℕ→ROp₂ _+'_ (f · tail g) (tail f · g)
    ≡⟨ refl ⟩
  liftℕ→ROp₂ (liftSeriesOp₂ _+_) (f · tail g) (tail f · g)
    ≡⟨ cong (λ p → p (f · tail g) (tail f · g)) 
        (transport⁻Transport 
          (λ i → Series≡ℕ→R i → Series≡ℕ→R i → Series≡ℕ→R i) 
          _+_
        )
    ⟩
  f · tail g + tail f · g
    ∎

·-unfold : ∀ f g → f · g ≡ (head f ·R head g) ∷ (f · tail g + tail f · g)
head (·-unfold f g i) = ·-head f g i
tail (·-unfold f g i) = ·-tail f g i

0s'≡0s : 0s' ≡ Series⟶ℕ→R 0s
0s'≡0s i 0 = 0R
0s'≡0s i (suc n) = 0s'≡0s i n

1s'≡1s : 1s' ≡ Series⟶ℕ→R 1s
1s'≡1s i 0 = 1R
1s'≡1s i (suc n) = 0s'≡0s i n

0s'-absorbL-n : ∀ f n → (0s' ·' f) n ≡ 0s' n
0s'-absorbL-n f 0 = 
  (0s' ·' f) 0
    ≡⟨ 0R-absorb-l (f 0) ⟩
  0R
    ∎
0s'-absorbL-n f (suc n) = 
  (0s' ·' f) (suc n) 
    ≡⟨ refl ⟩
  (0s' ·' f ⁺) n  +R  (0s' ·' f) n
    ≡⟨ cong₂ _+R_ 
        (0s'-absorbL-n (f ⁺) n)
        (0s'-absorbL-n f n)
    ⟩
  0R +R 0R
    ≡⟨ fst (+R-identity 0R) ⟩
  0R
    ≡⟨ refl ⟩
  0s' (suc n)
    ∎

0s'-absorbL : ∀ f → 0s' ·' f ≡ 0s'
0s'-absorbL f i n = 0s'-absorbL-n f n i

0s'-absorbR : ∀ f → f ·' 0s' ≡ 0s'
0s'-absorbR f = ·'-comm f 0s' ∙ 0s'-absorbL f

·'-identityˡ-n : ∀ f n → (1s' ·' f) n ≡ f n
·'-identityˡ-n f 0 = snd (·R-identity (f 0))
·'-identityˡ-n f (suc n) = 
  (1s' ·' f) (suc n) 
    ≡⟨ refl ⟩
  (1s' ·' (f ⁺)) n  +R  (0s' ·' f) n
    ≡⟨ cong₂ _+R_ (·'-identityˡ-n (f ⁺) n) (0s'-absorbL-n f n)  ⟩
  f (suc n) +R  0R
    ≡⟨ fst (+R-identity (f (suc n))) ⟩
  f (suc n)
    ∎

·'-identityˡ : ∀ f → 1s' ·' f ≡ f
·'-identityˡ f i n = ·'-identityˡ-n f n i

·'-identityʳ : ∀ f → f ·' 1s' ≡ f
·'-identityʳ f = ·'-comm f 1s' ∙ ·'-identityˡ f

mulp : PathP (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) _·'_ _·_
mulp i = 
  transp (λ j → Series≡ℕ→R (~ i ∨ ~ j) → Series≡ℕ→R (~ i ∨ ~ j) → Series≡ℕ→R (~ i ∨ ~ j)) (~ i) _·'_

·-assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
·-assoc = 
  transport 
    (λ i → (x y z : Series≡ℕ→R (~ i)) → 
      mulp i x (mulp i y z) ≡ mulp i (mulp i x y) z
    )
    ·'-assoc

onepInvAux : PathP (λ i → Series≡ℕ→R i) 1s (transport Series≡ℕ→R  1s)
onepInvAux = transport-filler Series≡ℕ→R 1s

onepInv : PathP (λ i → Series≡ℕ→R i) 1s 1s'
onepInv = subst (PathP (λ i → Series≡ℕ→R i) 1s) 
  (  
  transport Series≡ℕ→R 1s
    ≡[ i ]⟨ transport-isoToPath Series≃ℕ→R i  1s  ⟩
  Series⟶ℕ→R 1s
    ≡⟨ sym 1s'≡1s ⟩
  1s'
    ∎
  )
  onepInvAux

onep : PathP (λ i → Series≡ℕ→R (~ i)) 1s' 1s
onep i = onepInv (~ i)

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
