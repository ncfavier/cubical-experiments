open import 1Lab.Prelude
open import 1Lab.Path.Reasoning

module CoherentlyConstant where

data ∥_∥³ {ℓ} (A : Type ℓ) : Type ℓ where
  inc : A → ∥ A ∥³
  iconst : ∀ a b → inc a ≡ inc b
  icoh : ∀ a b c → PathP (λ i → inc a ≡ iconst b c i) (iconst a b) (iconst a c)
  squash : is-groupoid ∥ A ∥³

∥-∥³-elim-set
  : ∀ {ℓ ℓ'} {A : Type ℓ} {P : ∥ A ∥³ → Type ℓ'}
  → (∀ a → is-set (P a))
  → (f : (a : A) → P (inc a))
  → (∀ a b → PathP (λ i → P (iconst a b i)) (f a) (f b))
  → ∀ a → P a
∥-∥³-elim-set {P = P} sets f fconst = go where
  go : ∀ a → P a
  go (inc x) = f x
  go (iconst a b i) = fconst a b i
  go (icoh a b c i j) = is-set→squarep (λ i j → sets (icoh a b c i j))
    refl (λ i → go (iconst a b i)) (λ i → go (iconst a c i)) (λ i → go (iconst b c i))
    i j
  go (squash a b p q r s i j k) = is-hlevel→is-hlevel-dep 2 (λ _ → is-hlevel-suc 2 (sets _))
    (go a) (go b)
    (λ k → go (p k)) (λ k → go (q k))
    (λ j k → go (r j k)) (λ j k → go (s j k))
    (squash a b p q r s) i j k

∥-∥³-elim-prop
  : ∀ {ℓ ℓ'} {A : Type ℓ} {P : ∥ A ∥³ → Type ℓ'}
  → (∀ a → is-prop (P a))
  → (f : (a : A) → P (inc a))
  → ∀ a → P a
∥-∥³-elim-prop props f = ∥-∥³-elim-set (λ _ → is-hlevel-suc 1 (props _)) f
  (λ _ _ → is-prop→pathp (λ _ → props _) _ _)

∥-∥³-rec
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → is-groupoid B
  → (f : A → B)
  → (fconst : ∀ x y → f x ≡ f y)
  → (∀ x y z → fconst x y ∙ fconst y z ≡ fconst x z)
  → ∥ A ∥³ → B
∥-∥³-rec {A = A} {B} bgrpd f fconst fcoh = go where
  go : ∥ A ∥³ → B
  go (inc x) = f x
  go (iconst a b i) = fconst a b i
  go (icoh a b c i j) = ∙→square (sym (fcoh a b c)) i j
  go (squash x y a b p q i j k) = bgrpd
    (go x) (go y)
    (λ i → go (a i)) (λ i → go (b i))
    (λ i j → go (p i j)) (λ i j → go (q i j))
    i j k

∥-∥³-is-prop : ∀ {ℓ} {A : Type ℓ} → is-prop ∥ A ∥³
∥-∥³-is-prop = is-contr-if-inhabited→is-prop $
  ∥-∥³-elim-prop (λ _ → hlevel 1)
    (λ a → contr (inc a) (∥-∥³-elim-set (λ _ → squash _ _) (iconst a) (icoh a)))

∥-∥-rec-groupoid
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → is-groupoid B
  → (f : A → B)
  → (fconst : ∀ x y → f x ≡ f y)
  → (∀ x y z → fconst x y ∙ fconst y z ≡ fconst x z)
  → ∥ A ∥ → B
∥-∥-rec-groupoid bgrpd f fconst fcoh =
  ∥-∥³-rec bgrpd f fconst fcoh ∘ ∥-∥-rec ∥-∥³-is-prop inc
