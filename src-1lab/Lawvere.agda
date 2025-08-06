open import 1Lab.Prelude
open import Data.Power

-- Lawvere's fixed point theorem and related paradoxes.
module Lawvere where

private variable
  ℓ : Level
  A B : Type ℓ

module _ (f : A → A → B) where
  lawvere-worker : (g : B → B) (x : fibre f (λ a → g (f a a))) → Σ[ b ∈ B ] g b ≡ b
  lawvere-worker g (a , p) =
    let
      δ : A → B
      δ a = g (f a a)
    in (f a a , sym (p $ₚ a))

module _ (f : A → A → B) (f-surj : is-surjective f) where
  lawvere : (g : B → B) → ∃[ b ∈ B ] g b ≡ b
  lawvere g = lawvere-worker f g <$> f-surj _

Curry : A ≃ (A → B) → B
Curry e = lawvere-worker (e .fst) id (equiv-centre e _) .fst

module _ (f : A → ℙ A) (f-surj : is-surjective f) where
  cantor : ⊥
  cantor = ∥-∥-out! do
    A , fixed ← lawvere f f-surj ¬Ω_
    pure (Curry (path→equiv (ap ⌞_⌟ (sym fixed))))
