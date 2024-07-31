open import 1Lab.Classical
open import 1Lab.Prelude

open import Data.Dec

-- A weird constructive principle equivalent to Markov's principle + WLEM + ¬¬-shift
-- https://types.pl/@ncf/112854858302377592
-- https://x.com/ncfavier/status/1817846740944314834
module Mystery where

TNE : ∀ {ℓ} {P : Type ℓ} → ¬ ¬ ¬ P → ¬ P
TNE h p = h λ k → k p

case01 : ∀ {ℓ} {A : Type ℓ} → A → A → Nat → A
case01 z s zero = z
case01 z s (suc n) = s

mystery MP DNS : Type

mystery = (P : Nat → Ω) → (¬ ∀ n → ∣ P n ∣) → ∃ _ λ n → ¬ ∣ P n ∣

MP = (P : Nat → Ω) → (∀ n → Dec ∣ P n ∣) → (¬ ∀ n → ∣ P n ∣) → ∃ _ λ n → ¬ ∣ P n ∣

DNS = (P : Nat → Ω) → (∀ n → ¬ ¬ ∣ P n ∣) → ¬ ¬ ∀ n → ∣ P n ∣

mystery→MP : mystery → MP
mystery→MP m P _ = m P

mystery→WLEM : mystery → WLEM
mystery→WLEM m P = case m (case01 P (¬Ω P)) (λ h → h 1 (h 0)) of λ where
  zero    p → yes p
  (suc _) p → no p

mystery→DNS : mystery → DNS
mystery→DNS m P h k = case m P k of h

MP+WLEM+DNS→mystery : MP × WLEM × DNS → mystery
MP+WLEM+DNS→mystery (mp , wlem , dns) P h =
  mp (λ n → ¬Ω ¬Ω P n) (λ n → wlem (¬Ω P n)) (λ k → dns P k h)
  <&> Σ-map id TNE

mystery≃MP+WLEM+DNS : mystery ≃ (MP × WLEM × DNS)
mystery≃MP+WLEM+DNS = prop-ext!
  ⟨ mystery→MP , ⟨ mystery→WLEM , mystery→DNS ⟩ ⟩
  MP+WLEM+DNS→mystery
