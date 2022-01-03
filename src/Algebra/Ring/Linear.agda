{-# OPTIONS --guardedness --cubical #-}
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Module
module Algebra.Ring.Linear {ℓ ℓ' ℓ''} {R : Ring ℓ} (M : LeftModule R ℓ') (N : LeftModule R ℓ'') where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma
open import Cubical.Algebra.Ring

open RingStr (snd R) using (_·_; 1r) renaming (_+_ to _+r_)
open LeftModuleStr (snd M)
  renaming (_+_ to _+M_; 0m to 0M; _⋆_ to _⋆M_)
open LeftModuleStr (snd N)
  renaming (_+_ to _+N_; 0m to 0N; _⋆_ to _⋆N_)

linear-helper
  : (f : ⟨ M ⟩ → ⟨ N ⟩)
  → (∀ x y → f (x +M y) ≡ f x +N f y)
  → (∀ r x → f (r ⋆M x) ≡ r ⋆N f x)
  → ∀ r x s y
  → f ((r ⋆M x) +M (s ⋆M y)) ≡ (r ⋆N f x) +N (s ⋆N f y)
linear-helper f additive scalar r x s y = 
  f ((r ⋆M x) +M (s ⋆M y)) 
    ≡⟨ additive (r ⋆M x) (s ⋆M y) ⟩
  f (r ⋆M x) +N f (s ⋆M y)
    ≡⟨ cong₂ _+N_ (scalar r x) (scalar s y)  ⟩
  (r ⋆N f x) +N (s ⋆N f y)
    ∎
