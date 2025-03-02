open import Cat.Prelude
import Cat.Reasoning
open import 1Lab.Classical
open import Data.Dec
open import Data.Sum

-- If every split monomorphism with inhabited domain splits in Sets then excluded middle holds.
module SplitMonoSet where

module Sets = Cat.Reasoning (Sets lzero)

module _ (every-mono-splits : ∀ {A B} (a : ∥ ⌞ A ⌟ ∥) (f : Sets.Hom A B) (f-mono : Sets.is-monic {a = A} {B} f) → Sets.is-split-monic {a = A} {B} f) where
  lem : LEM
  lem P = ∥-∥-out! do
    Sets.make-retract f⁻¹ ret ← f-split
    pure (go (f⁻¹ (inr tt)) λ p → ret $ₚ inr p)
    where
    A : Set lzero
    A = el! (⊤ ⊎ ⌞ P ⌟)
    B : Set lzero
    B = el! (⊤ ⊎ ⊤)
    f : Sets.Hom A B
    f = ⊎-map _ _
    f-mono : Sets.is-monic {a = A} {B} f
    f-mono = embedding→monic {f = f} $ injective→is-embedding! λ where
      {inl _} {inl _} p → refl
      {inl _} {inr _} p → absurd (inl≠inr p)
      {inr _} {inl _} p → absurd (inr≠inl p)
      {inr _} {inr _} p → ap inr prop!
    f-split : Sets.is-split-monic {a = A} {B} f
    f-split = every-mono-splits (inc (inl _)) f λ {c} → f-mono {c}
    go : (f⁻¹r : ∣ A ∣) → (∀ p → f⁻¹r ≡ inr p) → Dec ∣ P ∣
    go (inl _) l = no λ p → inl≠inr (l p)
    go (inr p) l = yes p
