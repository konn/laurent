{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.CommRing
module Algebra.Ring.PowerSeries.Units {ℓ} (R : CommRing ℓ) where
open import Algebra.Ring.PowerSeries.Base R
open import Algebra.Ring.PowerSeries.Addition R
open import Algebra.Ring.PowerSeries.Multiplication R
open import Lemmas.IsoEquiv
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP
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

UnitConstant : ℙ PowerSeries
UnitConstant r = (head r ∈ R ˣ), ∈-isProp (R ˣ) (head r)

R₀ : Type _
R₀ = ⟨ R ⟩

open Units R using () renaming (_⁻¹ to _⁻¹R; ·-rinv  to ·R-rinv)
open import Cubical.Algebra.Ring.BigOps
open Sum (CommRing→Ring R) renaming (∑ to ∑R ; ∑Last to ∑RLast )

private
  variable
    ℓ' : Level
    A : Type ℓ'

snoc : ∀ {n} → FinVec A n → A → FinVec A (suc n)
snoc {n = 0} f an zero = an
snoc {n = suc n} f an zero = f zero
snoc {n = suc _} f an (suc n) = snoc (λ k → f (suc k)) an n

snoc-last : ∀ {n} → ∀ (f : FinVec A n) a → snoc f a (fromℕ n) ≡ a
snoc-last {n = 0} f a = refl
snoc-last {n = suc n} f a =
  snoc f a (fromℕ (suc n)) 
    ≡⟨ refl ⟩
  snoc f a (suc (fromℕ n))
    ≡⟨ refl ⟩
  snoc (f ∘ suc) a (fromℕ n)
    ≡⟨ snoc-last (f ∘ suc) a ⟩
  a
    ∎

seq-<-def-aux : (∀{n} → (Fin n → A) → A) → ∀ n → Fin (suc n) → A
seq-<-def-aux ind 0 zero = ind {n = 0} (λ ())
seq-<-def-aux ind (suc n) =
  let IH = seq-<-def-aux ind n
  in snoc IH (ind IH)

seq-<-def : (∀{n} → (Fin n → A) → A) → ℕ → A
seq-<-def ind n = seq-<-def-aux ind n (fromℕ n)

infix 9 _↾_
_↾_ : (ℕ → A) → ∀ n → Fin n → A
_↾_ f n o = f (toℕ o)

↾0 : ∀(f : ℕ → A) → f ↾ 0 ≡ (λ ())
↾0 f i ()

↾suc-snoc-n : ∀(f : ℕ → A) n → ∀ od → (f ↾ (suc n)) od ≡ snoc (f ↾ n) (f n) od
↾suc-snoc-n f 0 zero i = f 0
↾suc-snoc-n f (suc n) zero = refl
↾suc-snoc-n f (suc n) (suc k) =
  (f ↾ suc (suc n)) (suc k)
    ≡⟨ refl ⟩
  ((f ∘ suc) ↾ (suc n)) k
    ≡⟨ ↾suc-snoc-n (f ∘ suc) n k ⟩
  snoc ((f ∘ suc) ↾ n) (f (suc n)) k
    ≡⟨ refl ⟩
  snoc (f ↾ suc n) (f (suc n)) (suc k)
    ∎

↾suc-snoc : ∀(f : ℕ → A) n → f ↾ (suc n) ≡ snoc (f ↾ n) (f n)
↾suc-snoc f n i o = ↾suc-snoc-n f n o i

seq-<-def-↾ : ∀ (ind : (∀{n} → (Fin n → A) → A)) n →
  seq-<-def ind ↾ suc n ≡ seq-<-def-aux ind n
seq-<-def-↾ ind 0 = funExt (λ { zero → refl})
seq-<-def-↾ ind (suc n) =
  seq-<-def ind ↾ suc (suc n) 
    ≡⟨ ↾suc-snoc (seq-<-def ind) (suc n) ⟩
  snoc (seq-<-def ind ↾ (suc n)) (seq-<-def ind (suc n))
    ≡⟨ cong₂ snoc
      (seq-<-def-↾ ind n)
      (snoc-last (seq-<-def-aux ind n) (ind (seq-<-def-aux ind n)))
    ⟩
  snoc (seq-<-def-aux ind n) (ind (seq-<-def-aux ind n))
    ≡⟨ refl ⟩
  seq-<-def-aux ind (suc n)
    ∎

seq-<-def-unfold :
  ∀ (ind : (∀{n} → (Fin n → A) → A)) n → seq-<-def ind n ≡ ind (seq-<-def ind ↾ n)
seq-<-def-unfold ind 0 =
  seq-<-def ind 0
    ≡⟨ refl ⟩
  seq-<-def-aux ind 0 zero
    ≡⟨ refl ⟩
  ind {n = 0} (λ ())
    ≡⟨ cong (ind { n = 0}) (sym (↾0 (seq-<-def ind))) ⟩
  ind (seq-<-def ind ↾ 0)
    ∎
seq-<-def-unfold ind (suc n) =
  seq-<-def ind (suc n) 
    ≡⟨ refl ⟩
  seq-<-def-aux ind (suc n) (fromℕ (suc n))
    ≡⟨ refl ⟩
  snoc (seq-<-def-aux ind n) (ind (seq-<-def-aux ind n)) (fromℕ (suc n))
    ≡⟨ snoc-last (seq-<-def-aux ind n) _ ⟩
  ind (seq-<-def-aux ind n)
    ≡⟨ cong ind (sym (seq-<-def-↾ ind n)) ⟩
  ind (seq-<-def ind ↾ suc n)
    ∎

inv'-step : ∀ (f : ℕ → R₀) ⦃ _ : f 0 ∈ R ˣ ⦄ → ∀ {n} (g : Fin n → R₀) → R₀
inv'-step f {n = 0} g = f 0 ⁻¹R
inv'-step f {n = suc n} g = f 0 ⁻¹R ·R (-R (∑R λ i → f (suc n ∸ toℕ i) ·R g i ))

inv' : ∀ (f : ℕ → R₀) → ⦃ f 0 ∈ R ˣ ⦄ → ℕ → R₀
inv' f = seq-<-def (inv'-step f)

inv'-unfold-zero : ∀ (f : ℕ → R₀) ⦃ _ : f 0 ∈ R ˣ ⦄ → inv' f 0 ≡ f 0 ⁻¹R
inv'-unfold-zero f = refl

inv'-unfold-suc : ∀ (f : ℕ → R₀) ⦃ inv : f 0 ∈ R ˣ ⦄ →
  ∀ n → 
    inv' f (suc n)
    ≡ (f 0 ⁻¹R) ·R 
      (-R (∑R (λ (i : Fin (suc n)) → f (suc n ∸ toℕ i) ·R inv' f (toℕ i))))
inv'-unfold-suc f n = 
  inv' f (suc n)
    ≡⟨ seq-<-def-unfold (inv'-step f) (suc n) ⟩
  inv'-step f (inv' f ↾ (suc n))
    ≡⟨ refl ⟩
  f 0 ⁻¹R ·R (-R (∑R λ (i : Fin (suc n)) → f (suc n ∸ toℕ i) ·R inv' f (toℕ i) ))
    ∎

inv : ∀ (f : PowerSeries) → ⦃ head f ∈ R ˣ ⦄ → PowerSeries
inv = transport 
  (λ i → ∀ (f : Series≡ℕ→R (~ i)) → ⦃ headp i f ∈ R ˣ ⦄ → Series≡ℕ→R (~ i) ) 
  inv'

invp : PathP 
  (λ i → (f : Series≡ℕ→R (~ i)) → ⦃ _ : headp i f ∈ R ˣ ⦄ → Series≡ℕ→R (~ i))
  inv'
  inv
invp = 
  transport-filler
    (λ i → (f : Series≡ℕ→R (~ i)) → ⦃ _ : headp i f ∈ R ˣ ⦄ → Series≡ℕ→R (~ i))
    inv'

PowerSeriesˣ⊆UnitConstant : (Series-CommRing ˣ) ⊆ UnitConstant
PowerSeriesˣ⊆UnitConstant f (g , fg≡1) =
  (head g ,
    (head f ·R head g
      ≡⟨ sym (·-head f g) ⟩
    head (f · g)
      ≡⟨ cong head fg≡1 ⟩
    head 1s
      ≡⟨ refl ⟩
    1R
      ∎
    )
  )

f·'invF-n : ∀ f ⦃ _ : f 0 ∈ R ˣ ⦄ n → (f ·' inv' f) n ≡ 1s' n
f·'invF-n f 0 = 
  (f ·' inv' f) 0 
    ≡⟨ refl ⟩
  f 0 ·R (f 0 ⁻¹R)
    ≡⟨ ·R-rinv (f 0) ⟩
  1R
    ∎
f·'invF-n f (suc n) =
  (f ·' inv' f) (suc n)
    ≡⟨ ·'-explicit f (inv' f) (suc n) ⟩
  ∑R (λ(i : Fin (suc (suc n))) → f (suc n ∸ toℕ i) ·R inv' f (toℕ i) )
    ≡⟨ ∑RLast (λ(i : Fin (suc (suc n))) → f (suc n ∸ toℕ i) ·R inv' f (toℕ i) ) ⟩
  ∑R (λ(i : Fin (suc n)) → f (suc n ∸ toℕ (weakenFin i)) ·R inv' f (toℕ (weakenFin i)) )
    +R f (suc n ∸ toℕ (fromℕ (suc n))) ·R inv' f (toℕ (fromℕ (suc n)))
    ≡⟨ cong₂ _+R_
        (cong ∑R (funExt (λ (k : Fin (suc n)) → 
          cong 
            (λ z → f (suc n ∸ z) ·R inv' f z)
            (weakenRespToℕ k)
        )))
        (cong (λ z → f (suc n ∸ z) ·R inv' f z)
          (toFromId (suc n))
        )
    ⟩
  ∑R (λ(i : Fin (suc n)) → f (suc n ∸ toℕ i) ·R inv' f (toℕ i) )
    +R f (suc n ∸ suc n) ·R inv' f (suc n)
    ≡⟨ cong (∑R (λ(i : Fin (suc n)) → f (suc n ∸ toℕ i) ·R inv' f (toℕ i) ) +R_)
      (
        cong₂ (λ l r → f l ·R r)
          (n∸n≡0 (suc n))
          (inv'-unfold-suc f n)
          ∙ ·R-assoc (f 0) (f 0 ⁻¹R) _
          ∙ cong (_·R (-R (∑R (λ (i : Fin (suc n)) → f (suc n ∸ toℕ i) ·R inv' f (toℕ i))))) (·R-rinv (f 0))
          ∙ snd (·R-identity _)
      )
    ⟩
  ∑R (λ(i : Fin (suc n)) → f (suc n ∸ toℕ i) ·R inv' f (toℕ i) )
    +R (-R (∑R (λ (i : Fin (suc n)) → f (suc n ∸ toℕ i) ·R inv' f (toℕ i))))
    ≡⟨ +R-rinv _ ⟩
  0R
    ∎

·'-rinv : ∀ f ⦃ _ : f 0 ∈ R ˣ ⦄ → f ·' inv' f ≡ 1s'
·'-rinv f i n = f·'invF-n f n i

·-rinv : ∀ f ⦃ _ : head f ∈ R ˣ ⦄ → f · inv f ≡ 1s
·-rinv =
  transport
    (λ i → (f : Series≡ℕ→R (~ i)) →
      ⦃ _ : headp i f ∈ R ˣ ⦄ → mulp i f (invp i f) ≡ onep i
    )
    ·'-rinv

UnitConstant⊆PowerSeriesˣ : UnitConstant ⊆ (Series-CommRing ˣ)
UnitConstant⊆PowerSeriesˣ f f0∈Rˣ =
  let instance 
        _ : head f ∈ R ˣ
        _ = f0∈Rˣ
  in (inv f , ·-rinv f)

-- | The units in the formal power series ring is exactly those with unit coefficient.
PowerSeriesˣ≡UnitConstant : (Series-CommRing ˣ) ≡ UnitConstant
PowerSeriesˣ≡UnitConstant = 
  ⊆-extensionality (Series-CommRing ˣ) UnitConstant
    (PowerSeriesˣ⊆UnitConstant , UnitConstant⊆PowerSeriesˣ)
