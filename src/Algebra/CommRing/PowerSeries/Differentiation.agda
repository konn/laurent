{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.CommRing.PowerSeries.Differentiation {ℓ} (R : CommRing ℓ) where
open import Algebra.CommRing.PowerSeries.Base R
open import Algebra.CommRing.PowerSeries.Addition R
open import Algebra.CommRing.PowerSeries.Multiplication R
open import Algebra.CommRing.PowerSeries.Module R
open import Cubical.Data.Sigma
open import Cubical.Algebra.RingSolver.ReflectionSolving
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP
open import Cubical.Data.Nat
  using ( ℕ ; suc )
  renaming (_+_ to _+ℕ_; _·_ to _·ℕ_)

open PowerSeries
open import Algebra.Ring.FromNat (CommRing→Ring R)
import Algebra.Ring.Linear as Linear
open import Lemmas.IsoEquiv

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

-- * Derivative defined in terms of zipping.

-- | The series corresponding to @n + (1 + n) x + (2 + n) x^2 + ...@
natsFrom : ℕ → PowerSeries
head (natsFrom n) = fromNat n
tail (natsFrom n) = natsFrom (suc n)

-- | 0 + 1 x + 2 x^2 + ... + n x^n + ...
nats : PowerSeries
nats = natsFrom 0

open import Algebra.CommRing.PowerSeries.Zip R

-- | Formal derivative of formal power series, defined
-- in terms of zipping with naturals and then taking the tail-part.
diff : PowerSeries → PowerSeries
diff f = tail (nats ⊗ f)

_′ d/dx_ : PowerSeries → PowerSeries
_′ = diff
d/dx_ = _′

natsFrom' : ℕ → ℕ → ⟨ R ⟩
natsFrom' n m = fromNat m +R fromNat n

Series⟶∘natsFrom≡natsFrom'
  : ∀ n m → Series⟶ℕ→R (natsFrom n) m ≡ natsFrom' n m
Series⟶∘natsFrom≡natsFrom' n 0 = sym (snd (+R-identity (fromNat n)))
Series⟶∘natsFrom≡natsFrom' n (suc m) =
  Series⟶ℕ→R (natsFrom n) (suc m) 
    ≡⟨ refl ⟩
  Series⟶ℕ→R (natsFrom (suc n)) m
    ≡⟨ Series⟶∘natsFrom≡natsFrom' (suc n) m ⟩
  natsFrom' (suc n) m
    ≡⟨ cong (fromNat m +R_) (fromNat-suc n) ⟩
  fromNat m +R (1R +R fromNat n)
    ≡⟨(
      let pf : ∀ (a b : ⟨ R ⟩) → (a +R (1R +R b)) ≡ (1R +R a) +R b
          pf = solve R
      in pf (fromNat m) (fromNat n)
    )⟩
  (1R +R fromNat m) +R (fromNat n)
    ≡⟨ cong (_+R fromNat n) (sym (fromNat-suc m)) ⟩
  natsFrom' n (suc m)
    ∎

natsFromp⁻ : PathP (λ i → ℕ → Series≡ℕ→R i) natsFrom natsFrom'
natsFromp⁻ = funExt 
  (λ n →
  subst (PathP (λ i → Series≡ℕ→R i) (natsFrom n))
    (
      transport (λ i → Series≡ℕ→R i) (natsFrom n)
        ≡[ i ]⟨ transport-isoToPath Series≃ℕ→R i (natsFrom n) ⟩
      Series⟶ℕ→R (natsFrom n)
        ≡[ i ]⟨ (λ m → Series⟶∘natsFrom≡natsFrom' n m i) ⟩
      natsFrom' n
        ∎
    )
    (transport-filler (λ i → Series≡ℕ→R i) (natsFrom n))
  )

natsFromp : PathP (λ i → ℕ → Series≡ℕ→R (~ i)) natsFrom' natsFrom
natsFromp i = natsFromp⁻ (~ i)

natsFrom1 : ∀ n → natsFrom' 1 n ≡ fromNat (suc n)
natsFrom1 n = +R-comm (fromNat n) 1R ∙ sym (fromNat-suc n)

diff'≡natsFrom1⊗tail-n : ∀ f n → diff' f n ≡ (natsFrom' 1 ⊗' (f ⁺)) n
diff'≡natsFrom1⊗tail-n f n =
    diff' f n 
  ≡⟨ refl ⟩ 
    fromNat (suc n) ·R f (suc n)
  ≡⟨ cong (_·R f (suc n)) (sym (natsFrom1 n)) ⟩
    (natsFrom' 1 ⊗' (f ⁺)) n
  ∎

diff'≡natsFrom1⊗tail : ∀ f → diff' f ≡ natsFrom' 1 ⊗' (f ⁺)
diff'≡natsFrom1⊗tail f i n = diff'≡natsFrom1⊗tail-n f n i

diffp : PathP (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) diff' diff
diffp = 
  subst (λ d → PathP (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i)) d diff)
    (λ i f → diff'≡natsFrom1⊗tail f (~ i))
    aux
  where
    aux : 
      PathP (λ i → Series≡ℕ→R (~ i) → Series≡ℕ→R (~ i))
        (λ f → natsFrom' 1 ⊗' (f ⁺)) diff
    aux i f =
      zipp i (natsFromp i 1) (tailp i f)


diff≡[1…]⊗tail : ∀ f → diff f ≡ natsFrom 1 ⊗ tail f
diff≡[1…]⊗tail f = refl

diff-additive : ∀ f g → diff (f + g) ≡ diff f + diff g
diff-additive f g =
  diff (f + g)
    ≡⟨ refl ⟩
  tail (nats ⊗ (f + g))
    ≡⟨ cong tail (⊗Rdist+ nats f g) ⟩
  tail (nats ⊗ f + nats ⊗ g)
    ≡⟨ refl ⟩
  diff f + diff g
    ∎

diff-scalar : ∀ r f → diff (r ⋆ f) ≡ r ⋆ diff f
diff-scalar r f =
  diff (r ⋆ f) 
    ≡⟨ refl ⟩
  natsFrom 1 ⊗ (r ⋆ tail f)
    ≡⟨ ⊗-⋆-dist (natsFrom 1) r (tail f) ⟩
  r ⋆ diff f
    ∎

diff-linear : ∀ r x s y → diff (r ⋆ x + s ⋆ y) ≡ r ⋆ diff x + s ⋆ diff y
diff-linear = linear-helper diff diff-additive diff-scalar
  where open Linear pow-module pow-module

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
