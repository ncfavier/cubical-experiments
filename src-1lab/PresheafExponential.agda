open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Functor.Naturality
open import Cat.Instances.Presheaf.Limits
open import Cat.Instances.Presheaf.Exponentials
open import Cat.Diagram.Exponential
open import Cat.Diagram.Product
import Cat.Reasoning

module PresheafExponential {ℓ} {C : Precategory ℓ ℓ} where

module C = Cat.Reasoning C
module PSh = Cat.Reasoning (PSh ℓ C)
open Binary-products (PSh ℓ C) (PSh-products _ C)
open Cartesian-closed (PSh-closed C)

open Functor
open _=>_

module _ b a where
  open Exponential (has-exp a b)
    renaming (B^A to infixr 50 _^_)
    using () public

module _ (K L M : PSh.Ob) where

  internal-currying : M ^ (K ⊗₀ L) PSh.≅ (M ^ K) ^ L
  internal-currying = PSh.make-iso
    (λ where
      .η n f .η q (v , y) .η p (u , x) → f .η p (v C.∘ u , x , L .F₁ u y)
      .η n f .η q (v , y) .is-natural → {!   !}
      .η n f .is-natural → {!   !}
      .is-natural → {!   !})
    (λ where
      .η n g .η q (v , x , y) → g .η q (v , y) .η q (C.id , x)
      .η n g .is-natural → {!   !}
      .is-natural → {!   !})
    (ext λ n g q v y p u x →
      ⌜ g .η p (v C.∘ u , L .F₁ u y) ⌝ .η p (C.id , x) ≡⟨ g .is-natural _ _ u $ₚ (v , y) ηₚ p $ₚ (C.id , x) ⟩
      (M ^ K) .F₁ u (g .η q (v , y)) .η p (C.id , x)   ≡⟨⟩
      g .η q (v , y) .η p (⌜ u C.∘ C.id ⌝ , x)         ≡⟨ ap! (C.idr u) ⟩
      g .η q (v , y) .η p (u , x)                      ∎)
    {!   !}
