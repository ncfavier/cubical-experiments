open import 1Lab.Equiv
open import 1Lab.Extensionality
open import 1Lab.HLevel
open import 1Lab.HLevel.Closure
open import 1Lab.Path
open import 1Lab.Reflection.HLevel
open import 1Lab.Reflection.Record
open import 1Lab.Type
open import 1Lab.Type.Sigma

-- Applicative fully determines the underlying Functor.
module Applicative {ℓ} where

private variable
  A B C : Type ℓ

_∘'_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
     → (B → C) → (A → B) → A → C
f ∘' g = λ z → f (g z)

record applicative (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  infixl 5 _<*>_
  field
    sets : is-set (F A)
    pure : A → F A
    _<*>_ : F (A → B) → F A → F B
    <*>-identity : ∀ {u : F A}
      → pure id <*> u ≡ u
    <*>-composition : ∀ {u : F (B → C)} {v : F (A → B)} {w : F A}
      → pure _∘'_ <*> u <*> v <*> w ≡ u <*> (v <*> w)
    <*>-homomorphism : ∀ {f : A → B} {x : A}
      → pure f <*> pure x ≡ pure (f x)
    <*>-interchange : ∀ {u : F (A → B)} {x : A}
      → u <*> pure x ≡ pure (λ f → f x) <*> u

record applicative-functor (F : Type ℓ → Type ℓ) (app : applicative F) : Type (lsuc ℓ) where
  open applicative app
  infixl 5 _<$>_
  field
    _<$>_ : (A → B) → F A → F B
    <$>-identity : ∀ {x : F A}
      → id <$> x ≡ x
    <$>-composition : ∀ {f : B → C} {g : A → B} {x : F A}
      → f <$> (g <$> x) ≡ f ∘' g <$> x
    pure-natural : ∀ {f : A → B} {x : A}
      → f <$> pure x ≡ pure (f x)
    <*>-extranatural-A : ∀ {f : F (B → C)} {g : A → B} {x : F A}
      → f <*> (g <$> x) ≡ (_∘' g) <$> f <*> x
    <*>-natural-B : ∀ {g : B → C} {f : F (A → B)} {x : F A}
      → g <$> (f <*> x) ≡ (g ∘'_) <$> f <*> x

open applicative-functor
unquoteDecl eqv = declare-record-iso eqv (quote applicative-functor)

applicative-functor-path
  : ∀ {F : Type ℓ → Type ℓ} {app} {a b : applicative-functor F app}
  → (∀ {A B} (f : A → B) x → a ._<$>_ f x ≡ b ._<$>_ f x)
  → a ≡ b
applicative-functor-path {F = F} {app = app} p = Iso.injective eqv (Σ-prop-path! (ext λ f → p f))
  where instance
    F-sets : ∀ {x} → H-Level (F x) 2
    F-sets = hlevel-instance (app .applicative.sets)

applicative-determines-functor : ∀ {F} (app : applicative F)
  → is-contr (applicative-functor F app)
applicative-determines-functor {F} app = p where
  open applicative app
  p : is-contr (applicative-functor F app)
  p .centre ._<$>_ f x = pure f <*> x
  p .centre .<$>-identity = <*>-identity
  p .centre .<$>-composition {f = f} {g = g} {x = x} =
    pure f <*> (pure g <*> x) ≡⟨ sym <*>-composition ⟩
    pure _∘'_ <*> pure f <*> pure g <*> x ≡⟨ ap (λ y → y <*> pure g <*> x) <*>-homomorphism ⟩
    pure (f ∘'_) <*> pure g <*> x ≡⟨ ap (_<*> x) <*>-homomorphism ⟩
    pure (f ∘' g) <*> x ∎
  p .centre .pure-natural = <*>-homomorphism
  p .centre .<*>-extranatural-A {f = f} {g = g} {x = x} =
    f <*> (pure g <*> x) ≡⟨ sym <*>-composition ⟩
    pure _∘'_ <*> f <*> pure g <*> x ≡⟨ ap (_<*> x) <*>-interchange ⟩
    pure (_$ g) <*> (pure _∘'_ <*> f) <*> x ≡⟨ ap (_<*> x) (p .centre .<$>-composition) ⟩
    pure (_∘' g) <*> f <*> x ∎
  p .centre .<*>-natural-B {g = g} {f = f} {x = x} =
    pure g <*> (f <*> x) ≡⟨ sym <*>-composition ⟩
    pure _∘'_ <*> pure g <*> f <*> x ≡⟨ ap (λ y → y <*> f <*> x) <*>-homomorphism ⟩
    pure (g ∘'_) <*> f <*> x ∎
  p .paths app' = applicative-functor-path λ f x →
    pure f <*> x                ≡⟨ ap (_<*> x) (sym A.pure-natural) ⟩
    (f ∘'_) A.<$> pure id <*> x ≡˘⟨ A.<*>-natural-B ⟩
    f A.<$> (pure id <*> x)     ≡⟨ ap (f A.<$>_) <*>-identity ⟩
    f A.<$> x                   ∎
    where module A = applicative-functor app'
