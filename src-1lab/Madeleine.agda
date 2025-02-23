open import 1Lab.Prelude
open import 1Lab.Classical
open import Data.Sum
open import Data.Dec
open import Data.Bool
open import Meta.Invariant

module Madeleine where

axiom = ∀ {ℓ} {P Q : Type ℓ} ⦃ _ : H-Level P 1 ⦄ ⦃ _ : H-Level Q 1 ⦄ → ∥ P ⊎ Q ∥ → P ⊎ Q

lem→axiom : LEM → axiom
lem→axiom lem {P = P} {Q} pq with lem (elΩ P)
... | yes a = inl (□-out! a)
... | no ¬a = inr (rec! (λ { (inl p) → absurd (¬a (inc p)); (inr q) → q }) pq)

module _ (ε : axiom) where

  module _ {ℓ} {X : Type ℓ} ⦃ _ : H-Level X 2 ⦄ (a₀ a₁ : X) where
    E : X → Type _
    E x = (a₀ ≡ x) ⊎ (a₁ ≡ x)

    E' : Type _
    E' = Σ X λ x → ∥ E x ∥

    r : Bool → E'
    r true = a₀ , inc (inl refl)
    r false = a₁ , inc (inr refl)

    s : E' → Bool
    s (x , e) with ε e
    ... | inl _ = true
    ... | inr _ = false

    r-s : ∀ e → r (s e) ≡ e
    r-s (x , e) with ε e
    ... | inl p = Σ-prop-path! p
    ... | inr p = Σ-prop-path! p

    discrete : Dec (a₀ ≡ a₁)
    discrete = invmap
      (λ p → ap fst (right-inverse→injective r r-s p))
      (λ p → ap s (Σ-prop-path! p))
      (s (r true) ≡? s (r false))

  lem : LEM
  lem P = invmap (λ p → subst ∣_∣ (sym p) _) (λ p → Ω-ua (biimp _ (λ _ → p)))
    (discrete P ⊤Ω)
