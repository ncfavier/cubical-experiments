open import 1Lab.Prelude

module Untruncate where

point : ∀ {ℓ} (X : Type ℓ) → X → Type∙ ℓ
point X x = X , x

is-homogeneous : ∀ {ℓ} → Type ℓ → Type (lsuc ℓ)
is-homogeneous X = ∀ x y → point X x ≡ point X y

∥-∥-rec-const
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B)
  → (b : B)
  → (∀ x → b ≡ f x)
  → ∥ A ∥ → B
∥-∥-rec-const {A = A} {B} f b f-const x =
  ∥-∥-elim {P = λ _ → Singleton b} (λ _ → is-contr→is-prop (contr _ Singleton-is-contr))
    (λ x → f x , f-const x) x .fst

module _ {ℓ} (X : Type ℓ) (x : X) (hom : is-homogeneous X) where
  point′ : ∥ X ∥ → Type∙ ℓ
  point′ = ∥-∥-rec-const (point X) (point X x) (hom x)

  myst : (x : ∥ X ∥) → point′ x .fst
  myst x = point′ x .snd

  factored : myst ∘ inc ≡ id
  factored = refl
