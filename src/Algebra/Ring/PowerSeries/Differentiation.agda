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
  ; ·-comm to ·R-comm
  ; +Identity to +R-identity
  ; +Inv to +R-inverse
  ; ·Assoc to ·R-assoc
  ; ·Identity to ·R-identity
  ; is-set to R-isSet
  ; ·Rdist+ to R-·Rdist+
  ; ·Ldist+ to R-·Ldist+
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

diff'0≡⁺0 : ∀ f → diff' f 0 ≡ (f ⁺) 0
diff'0≡⁺0 f = snd (·R-identity (f 1))

open Variables

private
  R-distr3-L : ∀ r x y z → r ·R (x +R y +R z) ≡ r ·R x +R r ·R y +R r ·R z
  R-distr3-L = solve R

  x[yz]≡y[xz] : ∀ x y z → x ·R (y ·R z) ≡ y ·R (x ·R z)
  x[yz]≡y[xz] = solve R

  seq-lem0 : ∀ a b c d → a +' (b +' (c ·' d)) ≡ b +' (a +' (d ·' c))
  -- We wanted to use Reflection solver, but it seems
  -- it gets stuck in the ocean of transports...
  seq-lem0 a b c d = 
    a +' (b +' (c ·' d)) 
      ≡⟨ +'-assoc a b (c ·' d) ⟩
    (a +' b) +' (c ·' d)
      ≡⟨ cong₂ _+'_ 
        (+'-comm a b)
        (·'-comm c d)
      ⟩
    (b +' a) +' (d ·' c)
      ≡⟨ sym (+'-assoc b a (d ·' c)) ⟩
    b +' (a +' (d ·' c))
      ∎

⁺′-+-′⁺ : ∀ f g n → (f ⁺ ·' diff' g) n +R (g ⁺ ·' diff' f) n
  ≡ fromNat (suc (suc n)) ·R (f ⁺ ·' g ⁺) n
⁺′-+-′⁺ f g 0 =
  (f ⁺ ·' diff' g) 0 +R (g ⁺ ·' diff' f) 0
    ≡⟨ refl ⟩
  f 1 ·R (1R ·R g 1) +R g 1 ·R (1R ·R f 1)
    ≡⟨ cong₂ _+R_
        ( f 1 ·R (1R ·R g 1)
            ≡⟨ ·R-assoc (f 1) 1R (g 1) ⟩
          (f 1 ·R 1R) ·R g 1
            ≡⟨ cong (_·R g 1) (·R-comm (f 1) 1R) ⟩
          (1R ·R f 1) ·R g 1
            ≡⟨ sym (·R-assoc 1R (f 1) (g 1)) ⟩
          1R ·R (f 1 ·R g 1)
            ∎
        )
        ( g 1 ·R (1R ·R f 1)
            ≡⟨ ·R-comm (g 1) (1R ·R f 1) ⟩
          1R ·R f 1 ·R g 1
            ≡⟨ sym (·R-assoc 1R (f 1) (g 1)) ⟩
          1R ·R (f 1 ·R g 1)
            ∎
        )
    ⟩
  1R ·R (f 1 ·R g 1) +R 1R ·R (f 1 ·R g 1)
    ≡⟨ sym (R-·Ldist+ 1R 1R (f 1 ·R g 1)) ⟩
  fromNat 2 ·R (f ⁺ ·' g ⁺) 0
    ∎
⁺′-+-′⁺ f g (suc n) =
  (f ⁺ ·' diff' g) (suc n) +R (g ⁺ ·' diff' f) (suc n)
    ≡⟨ cong ((f ⁺ ·' diff' g) (suc n) +R_)
      (·'-comm-n (g ⁺) (diff' f) (suc n))
    ⟩
  (f⁺ 0 ·R diff' g (suc n) +R (f ⁺ ⁺ ·' diff' g) n)
    +R
  (diff' f 0 ·R g [2+n]  +R  ((diff' f) ⁺ ·' g ⁺) n)
    ≡⟨ cong₂ _+R_
        (cong (_+R (f ⁺ ⁺ ·' diff' g) n)
          (x[yz]≡y[xz] (f⁺ 0) (fromNat [2+n]) (g [2+n]))
        )
        (cong₂ _+R_
          (cong (_·R g [2+n]) (diff'-0 f))
          (cong (λ z → (z ·' g ⁺) n) (diff'-⁺ f))
        )
    ⟩ 
  (fromNat [2+n] ·R (f⁺ 0 ·R g [2+n]) +R (f ⁺ ⁺ ·' diff' g) n)
    +R
  ((f⁺ 0 ·R g [2+n])  +R  ((f ⁺ ⁺ +' diff' (f ⁺)) ·' g ⁺) n)
    ≡⟨( 
      let lem0 : ∀ r a b c → (r ·R a +R b) +R (a +R c) 
                  ≡ (1R +R r) ·R a +R (b +R c)
          lem0 = solve R
      in lem0 (fromNat [2+n]) (f⁺ 0 ·R g [2+n])
            ((f ⁺ ⁺ ·' diff' g) n)
            (((f ⁺ ⁺ +' diff' (f ⁺)) ·' g ⁺) n)
    )⟩ 
  fromNat [3+n] ·R (f⁺ 0 ·R g [2+n])
    +R
  ((f ⁺ ⁺ ·' diff' g) n  +R  ((f ⁺ ⁺ +' diff' (f ⁺)) ·' g ⁺) n)
    ≡⟨ cong (fromNat [3+n] ·R (f⁺ 0 ·R g [2+n]) +R_)
      (((f ⁺ ⁺ ·' diff' g) n  +R  ((f ⁺ ⁺ +' diff' (f ⁺)) ·' g ⁺) n
          ≡⟨ cong ((f ⁺ ⁺ ·' diff' g) n  +R_)
              (·'‿+'-distrib-r-n (f ⁺ ⁺) (diff' (f ⁺)) (g ⁺) n)
          ⟩
        (f ⁺ ⁺ ·' diff' g) n  +R  ((f ⁺ ⁺  ·' g ⁺) +' (diff' (f ⁺)  ·' g ⁺)) n
          ≡⟨ sym (+'-compwise-n (f ⁺ ⁺ ·' diff' g) _ n) ⟩
        ((f⁺ ⁺ ·' diff' g) +' ((f ⁺ ⁺  ·' g ⁺) +' (diff' f⁺ ·' g⁺))) n
          ≡⟨ cong (λ k → k n) (
              seq-lem0 (f⁺ ⁺ ·' diff' g) (f ⁺ ⁺  ·' g ⁺) (diff' f⁺) (g ⁺)
          )⟩
        ((f ⁺ ⁺  ·' g ⁺) +' ((f⁺ ⁺ ·' diff' g) +' (g⁺ ·' diff' f⁺))) n
          ≡⟨ +'-compwise-n (f ⁺ ⁺ ·' g ⁺) _ n ⟩
        ((f ⁺ ⁺  ·' g ⁺) n +R ((f⁺ ⁺ ·' diff' g) +' (g⁺ ·' diff' f⁺)) n)
          ≡⟨ cong ((f ⁺ ⁺  ·' g ⁺) n +R_) 
              (+'-compwise-n _ _ n ∙ ⁺′-+-′⁺ (f ⁺) g n)
          ⟩
        (f ⁺ ⁺  ·' g ⁺) n +R fromNat [2+n] ·R (f ⁺ ⁺  ·' g ⁺) n
          ≡⟨(
            let lem0 : ∀ r a → a +R (r ·R a) ≡ (1R +R r) ·R a
                lem0 = solve R
            in lem0 (fromNat [2+n]) ((f ⁺ ⁺  ·' g ⁺) n)
          )⟩
        fromNat [3+n] ·R (f ⁺ ⁺  ·' g ⁺) n
          ∎
      ))
    ⟩
  fromNat [3+n] ·R (f⁺ 0 ·R g [2+n])
    +R
  fromNat [3+n] ·R (f ⁺ ⁺  ·' g ⁺) n
    ≡⟨ sym (R-·Rdist+ (fromNat [3+n]) (f⁺ 0 ·R g [2+n]) ((f ⁺ ⁺  ·' g ⁺) n)) ⟩
  fromNat [3+n] ·R (f⁺ 0 ·R g [2+n] +R (f ⁺ ⁺  ·' g ⁺) n)
    ≡⟨ refl ⟩ 
  fromNat [3+n] ·R (f ⁺ ·' g ⁺) (suc n)
    ∎
  where
    f⁺ = f ⁺
    g⁺ = g ⁺
    [2+n] = suc (suc n)
    [3+n] = suc (suc (suc n))

leibniz'-n : ∀ f g n → diff' (f ·' g) n ≡ (f ·' diff' g  +'  diff' f ·' g) n
leibniz'-n f g 0 =
  diff' (f ·' g) 0
    ≡⟨ refl ⟩
  1R ·R (f ·' g) 1
    ≡⟨ snd (·R-identity ((f ·' g) 1)) ⟩
  (f ·' g) 1
    ≡⟨ refl ⟩
  f 0 ·R g 1 +R f 1 ·R g 0
    ≡⟨ cong₂ 
      _+R_
      (cong (f 0 ·R_) (sym (snd (·R-identity (g 1)))))
      (cong (_·R g 0) (sym (snd (·R-identity (f 1)))))
    ⟩
  f 0 ·R (1R ·R g 1)  +R  (1R ·R f 1) ·R g 0
    ≡⟨ refl ⟩
  (f ·' diff' g) 0  +R  (diff' f ·' g) 0
    ≡⟨ sym (+'-compwise-n (f ·' diff' g) (diff' f ·' g) 0) ⟩
  (f ·' diff' g  +'  diff' f ·' g) 0
    ∎
leibniz'-n f g (suc n) = [fg]′⇒nf ∙ sym fg′+f′g⇒nf
  where
    2+n = fromNat (suc (suc n))
    theGoal = 
          f 0 ·R (diff' g (suc n)) 
      +R  g 0 ·R (diff' f (suc n))
      +R  fromNat (suc (suc n)) ·R (f ⁺ ·' g ⁺) n
    fg′+f′g⇒nf : (f ·' diff' g +' diff' f ·' g) (suc n) ≡ theGoal
    fg′+f′g⇒nf =
      (f ·' diff' g +' diff' f ·' g) (suc n) 
        ≡⟨ +'-compwise-n (f ·' diff' g) (diff' f ·' g) (suc n) ⟩
      (f ·' diff' g) (suc n) +R (diff' f ·' g) (suc n) 
        ≡⟨ cong₂ _+R_ refl
          (·'-comm-n (diff' f) g (suc n))
        ⟩
      (f 0 ·R diff' g (suc n)  +R  (f ⁺ ·' diff' g) n)
          +R
      (g 0 ·R diff' f (suc n)  +R  (g ⁺ ·' diff' f) n)
        ≡⟨( 
          let lem0 : ∀ x y z w → (x +R y) +R (z +R w) ≡ (x +R z) +R (y +R w)
              lem0 = solve R
          in lem0 
              (f 0 ·R diff' g (suc n))
              ((f ⁺ ·' diff' g) n)
              (g 0 ·R diff' f (suc n))
              ((g ⁺ ·' diff' f) n)
        )⟩
      f 0 ·R (diff' g (suc n))
        +R  g 0 ·R (diff' f (suc n))
        +R ((f ⁺ ·' diff' g) n +R (g ⁺ ·' diff' f) n)
        ≡⟨ cong
          (f 0 ·R (diff' g (suc n)) +R  g 0 ·R (diff' f (suc n)) +R_)
          (⁺′-+-′⁺ f g n)
        ⟩
      f 0 ·R (diff' g (suc n))
        +R  g 0 ·R (diff' f (suc n))
        +R  2+n ·R (f ⁺ ·' g ⁺) n
        ∎
    [fg]′⇒nf : diff' (f ·' g) (suc n) ≡ theGoal
    [fg]′⇒nf = 
      diff' (f ·' g) (suc n)
        ≡⟨ refl ⟩
      2+n ·R ((f ·' g) ⁺) (suc n)
        ≡⟨ cong (λ x → 2+n ·R x (suc n)) (·'‿⁺-unfold f g) ⟩
      2+n ·R (f 0 ⋆' g ⁺ +' (f ⁺ ·' g ⁺) ·' X' +' g 0 ⋆' f ⁺) (suc n)
        ≡⟨ cong (2+n ·R_) 
            (+'-+'-+'-compwise
                (f 0 ⋆' g ⁺)
                ((f ⁺ ·' g ⁺) ·' X')
                (g 0 ⋆' f ⁺)
                (suc n)
              )
        ⟩
      2+n ·R 
        ( (f 0 ⋆' g ⁺) (suc n) 
          +R ((f ⁺ ·' g ⁺) ·' X') (suc n) 
          +R (g 0 ⋆' f ⁺)  (suc n)
        )
        ≡⟨ R-distr3-L 2+n 
            ((f 0 ⋆' g ⁺) (suc n)) 
            (((f ⁺ ·' g ⁺) ·' X') (suc n) )
            ((g 0 ⋆' f ⁺)  (suc n))
        ⟩
      2+n ·R (f 0 ·R g (suc (suc n))) 
        +R 2+n ·R ((f ⁺ ·' g ⁺) ·' X') (suc n) 
        +R 2+n ·R (g 0 ·R f (suc (suc n)))
        ≡⟨ cong₂ _+R_ 
            (cong₂ _+R_ 
              (x[yz]≡y[xz] 2+n (f 0) (g (suc (suc n))))
              (cong (2+n ·R_) (X'-shift-n (f ⁺ ·' g ⁺) n))
            )
            (x[yz]≡y[xz] 2+n (g 0) (f (suc (suc n))))
        ⟩
      f 0 ·R (diff' g (suc n))
        +R 2+n ·R (f ⁺ ·' g ⁺) n
        +R g 0 ·R (diff' f (suc n))
        ≡⟨( let lem0 : ∀ x y z → x +R y +R z ≡ x +R z +R y
                lem0 = solve R
             in lem0
                  (f 0 ·R (diff' g (suc n)))
                  (2+n ·R ((f ⁺ ·' g ⁺)  n))
                  (g 0 ·R (diff' f (suc n)))
          )
        ⟩
          f 0 ·R (diff' g (suc n))
      +R  g 0 ·R (diff' f (suc n))
      +R  2+n ·R (f ⁺ ·' g ⁺) n
        ∎

leibniz' : ∀ f g → diff' (f ·' g) ≡ f ·' diff' g  +'  diff' f ·' g
leibniz' f g i n = leibniz'-n f g n i

leibniz : ∀ f g → (f · g)′ ≡ f · g ′  +  f ′ · g
leibniz =
  transport
    (λ i → (f g : Series≡ℕ→R (~ i)) →
      diffp i (mulp i f g) ≡ 
        addp i (mulp i f (diffp i g)) (mulp i (diffp i f) g)
    )
    leibniz'

