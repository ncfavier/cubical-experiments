open import 1Lab.Prelude
open import Homotopy.Connectedness
open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Functor.Properties

-- eso + full-on-isos functors have monoidal fibres.
module MonoidalFibres where

private variable
  o ℓ : Level
  C D : Precategory o ℓ

monoidal-fibres
  : ∀ {F : Functor C D}
  → is-category C → is-category D
  → is-eso F → is-full-on-isos F
  → ∀ y → is-connected (Essential-fibre F y)
monoidal-fibres {D = D} {F = F} ccat dcat eso full≅ y =
  ∥-∥-rec! (λ (y′ , Fy′≅y) → is-connected∙→is-connected {X = _ , y′ , Fy′≅y} λ (x , Fx≅y) → do
    (x≅y′ , eq) ← full≅ (Fx≅y ∘Iso (Fy′≅y Iso⁻¹))
    pure (Σ-pathp (ccat .to-path x≅y′)
      (≅-pathp _ _ (transport (λ i → PathP (λ j → Hom (F-map-path ccat dcat F x≅y′ (~ i) j) y) (Fx≅y .to) (Fy′≅y .to))
        (Hom-pathp-refll-iso (sym (ap from (Iso-swapl (sym eq))))))))
  ) (eso y)
  where open Univalent dcat
