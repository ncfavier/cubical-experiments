open import 1Lab.Prelude

open import Data.Dec
open import Data.Fin
open import Data.Fin.Closure

module Probability where

-- “I have two children, (at least) one of whom is a boy born on a Tuesday -
-- what is the probability that both children are boys?”

-- Simplifying assumptions: gender is binary; gender and day of birth are
-- uniformly distributed.
Gender = Fin 2
Day = Fin 7
Child = Fin 2

Sample = Child → Day × Gender

count : (A : Sample → Type) → ⦃ ∀ {s} → Finite (A s) ⦄ → Nat
count A = cardinality {A = Σ Sample A}

condition : Sample → Type
condition s = ∃[ i ∈ Child ] s i ≡ (1 , 1)

event : Sample → Type
event s = (i : Child) → s i .snd ≡ 1

answer : Nat × Nat -- formal fraction
answer = count (λ s → event s × condition s) , count condition

_ : answer ≡ (13 , 27)
_ = refl
