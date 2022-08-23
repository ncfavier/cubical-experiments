module Torus where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.Torus

private
  variable
    ℓ : Level
    A : Type ℓ

-- 🍩
data T² : Type where
  base : T²
  p q : base ≡ base
  surf : p ∙ q ≡ q ∙ p

hcomp-inv : {φ : I} (u : I → Partial φ A) (u0 : A [ φ ↦ u i1 ])
          → hcomp u (hcomp (λ k → u (~ k)) (outS u0)) ≡ outS u0
hcomp-inv u u0 i = hcomp-equivFiller (λ k → u (~ k)) u0 (~ i)

T²≃Torus : T² ≃ Torus
T²≃Torus = isoToEquiv (iso to from to-from from-to)
  where
    sides : {a : A} (p1 p2 : a ≡ a) (i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A
    sides p1 p2 i j k (i = i0) = compPath-filler p2 p1 (~ k) j
    sides p1 p2 i j k (i = i1) = compPath-filler' p1 p2 (~ k) j
    sides p1 p2 i j k (j = i0) = p1 (i ∧ k)
    sides p1 p2 i j k (j = i1) = p1 (i ∨ ~ k)

    to : T² → Torus
    to base = point
    to (p i) = line1 i
    to (q j) = line2 j
    to (surf i j) = hcomp (λ k → sides line1 line2 (~ i) j (~ k)) (square (~ i) j)

    from : Torus → T²
    from point = base
    from (line1 i) = p i
    from (line2 j) = q j
    from (square i j) = hcomp (sides p q i j) (surf (~ i) j)

    to-from : ∀ x → to (from x) ≡ x
    to-from point = refl
    to-from (line1 i) = refl
    to-from (line2 i) = refl
    to-from (square i j) = hcomp-inv (sides line1 line2 i j) (inS (square i j))

    from-to : ∀ x → from (to x) ≡ x
    from-to base = refl
    from-to (p i) = refl
    from-to (q i) = refl
    from-to (surf i j) = {! hcomp-inv (λ k → sides p q (~ i) j (~ k)) (inS (surf i j)) !}
      -- see https://github.com/agda/cubical/pull/912 for the full proof
