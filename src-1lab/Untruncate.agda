open import 1Lab.Prelude

-- The identity function on homogeneous types "factors" through the propositional truncation
-- (https://homotopytypetheory.org/2013/10/28/the-truncation-map-_-%E2%84%95-%E2%80%96%E2%84%95%E2%80%96-is-nearly-invertible)
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

module old {ℓ} (X : Type ℓ) (x : X) (hom : is-homogeneous X) where
  point' : ∥ X ∥ → Type∙ ℓ
  point' = ∥-∥-rec-const (point X) (point X x) (hom x)

  myst : (x : ∥ X ∥) → point' x .fst
  myst x = point' x .snd

  _ : myst ∘ inc ≡ id
  _ = refl

-- Simplification by David Wärn https://gist.github.com/dwarn/31d7002a5ca8df0443b31501056e357f
module new {ℓ : Level} {X : Type ℓ} where
  fam : ∥ X ∥ → n-Type ℓ 0
  fam = rec! λ x → el (Singleton x) (contr _ Singleton-is-contr)

  magic : X → X
  magic = fst ∘ centre ∘ is-tr ∘ fam ∘ inc

  _ : magic ≡ id
  _ = refl
