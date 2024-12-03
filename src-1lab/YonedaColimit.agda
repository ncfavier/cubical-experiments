open import Cat.Prelude
open import Cat.Functor.Hom
open import Cat.Functor.Base
open import Cat.Functor.Constant
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Terminal
open import Cat.CartesianClosed.Instances.PSh

import Cat.Reasoning

open _=>_
open make-is-colimit

module YonedaColimit {o ℓ} (C : Precategory o ℓ) where

open Cat.Reasoning C

Δ1 : Terminal (PSh ℓ C)
Δ1 = PSh-terminal {C = C}

open Terminal Δ1

よ-colimit : Colimit (よ C)
よ-colimit = to-colimit (to-is-colimit colim) where
  colim : make-is-colimit (よ C) top
  colim .ψ c = !
  colim .commutes f = ext λ _ _ → refl
  colim .universal eta comm .η x _ = eta x .η x id
  colim .universal eta comm .is-natural x y f = ext λ _ →
    sym (comm f ηₚ y $ₚ id) ·· ap (eta x .η y) id-comm ·· eta x .is-natural _ _ f $ₚ id
  colim .factors eta comm = ext λ x f →
    sym (comm f ηₚ x $ₚ id) ∙ ap (eta _ .η x) (idr _)
  colim .unique eta comm univ' fac' = ext λ x _ → fac' x ηₚ x $ₚ id
