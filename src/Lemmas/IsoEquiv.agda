{-# OPTIONS --guardedness --cubical #-}
module Lemmas.IsoEquiv where
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

invEqIsoToEquiv : (σ : Iso A B) → invEq (isoToEquiv σ) ≡ Iso.inv σ
invEqIsoToEquiv σ i y = Iso.inv σ y

isoToPath≡uaIsoToEquiv :
  (σ : Iso A B) → isoToPath σ ≡ ua (isoToEquiv σ)
isoToPath≡uaIsoToEquiv σ = refl

isoToEquivInvIso
  : ∀ (σ : Iso A B) → isoToEquiv (invIso σ) ≡ invEquiv (isoToEquiv σ)
isoToEquivInvIso σ = equivEq refl

isoToPathInvIso : ∀ (σ : Iso A B) → 
  isoToPath (invIso σ) ≡ sym (isoToPath σ)
isoToPathInvIso σ = 
  isoToPath (invIso σ) 
    ≡⟨ isoToPath≡uaIsoToEquiv (invIso σ) ⟩
  ua (isoToEquiv (invIso σ))
    ≡⟨ cong ua (isoToEquivInvIso σ) ⟩
  ua (invEquiv (isoToEquiv σ))
    ≡⟨ uaInvEquiv (isoToEquiv σ)  ⟩
  sym (ua (isoToEquiv σ))
    ≡⟨ cong sym (sym (isoToPath≡uaIsoToEquiv σ))  ⟩
  sym (isoToPath σ)
    ∎

isoη : ∀(σ : Iso A B)
  → σ ≡ iso (Iso.fun σ) (Iso.inv σ) (Iso.rightInv σ) (Iso.leftInv σ)
Iso.fun (isoη σ i) = Iso.fun σ
Iso.inv (isoη σ i) = Iso.inv σ
Iso.leftInv (isoη σ i) = Iso.leftInv σ
Iso.rightInv (isoη σ i) = Iso.rightInv σ

transport-isoToPath : ∀(σ : Iso A B) →  
  transport (isoToPath σ) ≡ Iso.fun σ
transport-isoToPath σ i x = transportRefl (Iso.fun σ x) i

transport⁻-isoToPath : ∀(σ : Iso A B) (y : B) →  
  transport⁻ (isoToPath σ) y ≡ Iso.inv σ y
transport⁻-isoToPath σ y =
    transport⁻ (isoToPath σ) y
  ≡⟨ refl ⟩
    transport (sym (isoToPath σ)) y
  ≡⟨ cong (λ p → transport p y) (sym (isoToPathInvIso σ)) ⟩
   transport (isoToPath (invIso σ)) y
  ≡[ i ]⟨ transport-isoToPath (invIso σ) i y  ⟩
    Iso.fun (invIso σ) y
  ≡⟨ refl ⟩
    Iso.inv σ y
  ∎

transportIsoToPathOp₂ :
  ∀(σ : Iso A B) (f : A → A → A) (x y : B)
  → transport (λ i → isoToPath σ i → isoToPath σ i → isoToPath σ i) f x y
    ≡ Iso.fun σ (f (Iso.inv σ x) (Iso.inv σ y))
transportIsoToPathOp₂ σ f x y =
    transport (λ i → isoToPath σ i → isoToPath σ i → isoToPath σ i) f x y
  ≡⟨ refl ⟩
    transport (λ i → ua (isoToEquiv σ) i → ua (isoToEquiv σ) i → ua (isoToEquiv σ) i) f x y
  ≡⟨ transportUAop₂ (isoToEquiv σ) f x y ⟩
    Iso.fun σ (f (invEq (isoToEquiv σ) x) (invEq (isoToEquiv σ) y))
  ≡⟨ cong₂ (λ l r → Iso.fun σ (f l r)) 
        (λ i →  invEqIsoToEquiv σ i x) 
        (λ i →  invEqIsoToEquiv σ i y)
    ⟩
    Iso.fun σ (f (Iso.inv σ x) (Iso.inv σ y))
  ∎

transport⁻IsoToPathOp₂ :
  ∀(σ : Iso A B) (f : B → B → B) (x y : A)
  → transport⁻ (λ i → isoToPath σ i → isoToPath σ i → isoToPath σ i) f x y
    ≡ Iso.inv σ (f (Iso.fun σ x) (Iso.fun σ y))
transport⁻IsoToPathOp₂ σ f x y =
    transport⁻ (λ i → isoToPath σ i → isoToPath σ i → isoToPath σ i) f x y
  ≡⟨ refl ⟩
    transport (λ i → sym (isoToPath σ) i → sym (isoToPath σ) i → sym (isoToPath σ) i) f x y
  ≡⟨ cong (λ p → transport (λ i → p i → p i → p i) f x y) 
      (sym (isoToPathInvIso  σ) )
  ⟩
    transport (λ i → isoToPath (invIso σ) i → isoToPath (invIso σ) i → isoToPath (invIso σ) i) f x y
  ≡⟨ transportIsoToPathOp₂ (invIso σ) f x y  ⟩
    Iso.fun (invIso σ) (f (Iso.inv (invIso σ) x) (Iso.inv (invIso σ) y))
  ≡⟨ refl ⟩
    Iso.inv σ (f (Iso.fun σ x) (Iso.fun σ y))
  ∎
