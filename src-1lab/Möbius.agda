open import 1Lab.Prelude

open import Data.Int renaming (Int to ℤ)

open import Homotopy.Space.Circle

open Equiv ΩS¹≃Int renaming (from to loopⁿ) using ()

-- https://math.stackexchange.com/questions/4940313/giving-calculating-explicit-homomorphism-between-fundamental-groups
module Möbius where

data Möbius : Type where
  up down : Möbius
  seam : up ≡ down
  top : up ≡ down
  bottom : down ≡ up
  surf : PathP (λ i → top i ≡ bottom i) seam (sym seam)

Cover : Möbius → Type
Cover up = ℤ
Cover down = ℤ
Cover (seam i) = ℤ
Cover (top i) = ua suc-equiv i
Cover (bottom i) = ua suc-equiv i
Cover (surf i j) = ua suc-equiv i

decode : ∀ {x} → up ≡ x → Cover x
decode p = subst Cover p 0

ι : S¹ → Möbius
ι = S¹-rec up (top ∙ bottom)

ι* : ℤ → ℤ
ι* = decode ∘ ap ι ∘ loopⁿ

_ : ι* 1 ≡ 2
_ = refl
