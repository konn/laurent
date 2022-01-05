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

open Units R using () renaming (_⁻¹ to _⁻¹R)
open import Cubical.Algebra.Ring.BigOps
open Sum (CommRing→Ring R) renaming (∑ to ∑R)

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

inv-aux : ∀ (f : ℕ → R₀) → ⦃ f 0 ∈ R ˣ ⦄ → ℕ → R₀
inv-aux f = seq-<-def (λ {n} g → aux n g)
  where
    invf0 = f 0 ⁻¹R
    aux : ∀ n (g : Fin n → R₀) → R₀
    aux 0 g = invf0
    aux (suc n) g = invf0 ·R (-R (∑R λ i → f (suc n ∸ toℕ i) ·R g i ))
