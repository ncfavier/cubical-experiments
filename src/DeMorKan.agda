module DeMorKan where

open import Cubical.Foundations.Prelude

-- The built-in I lives in its own "non-fibrant" universe, so Agda won't let
-- us express partial elements and subtypes.
-- Hence we define a "wrapper" HIT, but do not make use of its Kan structure!
data Interval : Type where
  i0' : Interval
  i1' : Interval
  inI : i0' ≡ i1'

module 2D (i j : I) where
  ⊔ : I
  ⊔ = ~ j ∨ i ∨ ~ i
  B L R : I → I
  B i = i ∨ ~ i    --
  L j = i1         -- replace these with anything (as long as they agree on endpoints)
  R j = ~ j        --
  horn : Partial ⊔ Interval
  horn (j = i0) = inI (B i)
  horn (i = i0) = inI (L j)
  horn (i = i1) = inI (R j)
  filler : Interval [ ⊔ ↦ horn ]
  filler = inS (inI ((~ j ∧ B i) ∨ (~ i ∧ L j) ∨ (i ∧ R j)))

module 3D (i j k : I) where
  ⊔ : I
  ⊔ = ~ k ∨ ~ i ∨ i ∨ ~ j ∨ j
  B L R D U : I → I → I
  B i j = i0
  L j k = i0
  R j k = i0
  D i k = i0
  U i k = i0
  horn : Partial ⊔ Interval
  horn (k = i0) = inI (B i j)
  horn (i = i0) = inI (L j k)
  horn (i = i1) = inI (R j k)
  horn (j = i0) = inI (D i k)
  horn (j = i1) = inI (U i k)
  filler : Interval [ ⊔ ↦ horn ]
  filler = inS (inI ((~ k ∧ B i j) ∨ (~ i ∧ L j k) ∨ (i ∧ R j k) ∨ (~ j ∧ D i k) ∨ (j ∧ U i k)))
