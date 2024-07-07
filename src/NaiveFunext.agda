{-# OPTIONS --without-K #-}
open import Agda.Primitive renaming (Set to Type)
open import Data.Product
open import Data.Product.Properties
open import Relation.Binary.PropositionalEquality

-- Naïve function extensionality implies function extensionality (HoTT book exercise 4.9)
module NaiveFunext where

private variable
  ℓ ℓ' : Level
  A : Type ℓ
  B : A → Type ℓ
  f g : (a : A) → B a

_~_ : (f g : (a : A) → B a) → Type _
f ~ g = ∀ a → f a ≡ g a

happly : f ≡ g → f ~ g
happly {f = f} p = subst (λ x → f ~ x) p λ _ → refl

cong-proj₂ : ∀ {a b} {c : B a} {d : B b} → (p : (a , c) ≡ (b , d)) → subst B (cong proj₁ p) c ≡ d
cong-proj₂ {c = c} refl = refl

singleton-is-contr : ∀ {a : A} {s : Σ A (a ≡_)} → (a , refl) ≡ s
singleton-is-contr {s = _ , refl} = refl

module _
  (ext : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {f g : (a : A) → B a} → f ~ g → f ≡ g)
  where

  module _ (f : (a : A) → B a) where
    r : ((a : A) → Σ _ (f a ≡_)) → Σ _ (f ~_)
    r p = (λ a → p a .proj₁) , (λ a → p a .proj₂)
    htpy-is-contr : (g : Σ _ (f ~_)) → (f , λ _ → refl) ≡ g
    htpy-is-contr _ = cong r (ext λ _ → singleton-is-contr)

  ext' : f ~ g → f ≡ g
  ext' {f = f} {g = g} h = cong proj₁ (htpy-is-contr f (g , h))

  retract : (h : f ~ g) → happly (ext' h) ≡ h
  retract {f = f} {g = g} h = cong-proj₂ (htpy-is-contr f (g , h))
