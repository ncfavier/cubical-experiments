open import Cat.Functor.Adjoint
open import Cat.Functor.Equivalence
open import Cat.Instances.Comma
open import Cat.Prelude

import Cat.Reasoning

open ↓Hom
open ↓Obj
open Functor
open is-iso
open is-precat-iso

-- An adjunction F ⊣ G induces an isomorphism of comma categories F ↓ 1 ≅ 1 ↓ G
module AdjunctionCommaIso where

module _
  {oc ℓc od ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
  {F : Functor C D} {G : Functor D C} (F⊣G : F ⊣ G)
  where

  module C = Cat.Reasoning C
  module D = Cat.Reasoning D

  to : Functor (F ↓ Id) (Id ↓ G)
  to .F₀ o .x = o .x
  to .F₀ o .y = o .y
  to .F₀ o .map = L-adjunct F⊣G (o .map)
  to .F₁ f .α = f .α
  to .F₁ f .β = f .β
  to .F₁ {a} {b} f .sq =
    L-adjunct F⊣G (b .map) C.∘ f .α         ≡˘⟨ L-adjunct-naturall F⊣G _ _ ⟩
    L-adjunct F⊣G (b .map D.∘ F .F₁ (f .α)) ≡⟨ ap (L-adjunct F⊣G) (f .sq) ⟩
    L-adjunct F⊣G (f .β D.∘ a .map)         ≡⟨ L-adjunct-naturalr F⊣G _ _ ⟩
    G .F₁ (f .β) C.∘ L-adjunct F⊣G (a .map) ∎
  to .F-id = trivial!
  to .F-∘ _ _ = trivial!

  to-is-precat-iso : is-precat-iso to
  to-is-precat-iso .has-is-ff = is-iso→is-equiv is where
    is : ∀ {a b} → is-iso (to .F₁ {a} {b})
    is .inv f .α = f .α
    is .inv f .β = f .β
    is {a} {b} .inv f .sq = Equiv.injective (adjunct-hom-equiv F⊣G) $
      L-adjunct F⊣G (b .map D.∘ F .F₁ (f .α)) ≡⟨ L-adjunct-naturall F⊣G _ _ ⟩
      L-adjunct F⊣G (b .map) C.∘ f .α         ≡⟨ f .sq ⟩
      G .F₁ (f .β) C.∘ L-adjunct F⊣G (a .map) ≡˘⟨ L-adjunct-naturalr F⊣G _ _ ⟩
      L-adjunct F⊣G (f .β D.∘ a .map)         ∎
    is .rinv f = trivial!
    is .linv f = trivial!
  to-is-precat-iso .has-is-iso = is-iso→is-equiv is where
    is : is-iso (to .F₀)
    is .inv o .x = o .x
    is .inv o .y = o .y
    is .inv o .map = R-adjunct F⊣G (o .map)
    is .rinv o = ↓Obj-path _ _ refl refl (L-R-adjunct F⊣G _)
    is .linv o = ↓Obj-path _ _ refl refl (R-L-adjunct F⊣G _)
