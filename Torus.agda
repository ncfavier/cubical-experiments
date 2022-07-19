module Torus where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.HITs.Torus

private
  variable
    ℓ : Level
    A : Type ℓ

data T² : Type where
  base : T²
  p q : base ≡ base
  surf : p ∙ q ≡ q ∙ p

T²≃Torus : Iso T² Torus
T²≃Torus = iso to from {!   !} {!   !}
  where
    to : T² → Torus
    to base = point
    to (p i) = line1 i
    to (q j) = line2 j
    to (surf i j) = surf' i j
      where
        surf' = cong (line1 ∙_) (sym (PathP→compPathL square)) ∙ compPathl-cancel _ _

    from : Torus → T²
    from point = base
    from (line1 i) = p i
    from (line2 j) = q j
    from (square i j) = {! !}
      where
        foo : Square (refl ∙ refl) (q ∙ refl) p (q ∙ p)
        foo = flipSquare (compPath-filler p q) ∙₂ flipSquare surf
        bar : Square refl (sym q) (sym p) (sym p ∙ sym q)
        bar = flipSquare (compPath-filler (sym p) (sym q))
        -- square' : Square (refl ∙ q) (q ∙ refl) p p
        square' = compPathP foo (λ i j → compPath-filler (sym p) (sym q) (~ i) (~ j))
