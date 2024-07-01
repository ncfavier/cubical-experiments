open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Functor.Compose
open import Cat.Functor.Equivalence.Path
open import Cat.Monoidal.Base
open import Cat.Monoidal.Diagram.Monoid
open import Cat.Instances.Product
open import Cat.Displayed.Base
open import Cat.Displayed.Total

open Monoidal-category
open Precategory
open Functor
open _=>_

module PointwiseMonoidal
  {o o′ ℓ ℓ′} (C : Precategory o ℓ) (D : Precategory o′ ℓ′)
  (M : Monoidal-category D)
  where

Pointwise : Monoidal-category Cat[ C , D ]
Pointwise = pw where
  prod : Functor (Cat[ C , D ] ×ᶜ Cat[ C , D ]) Cat[ C , D ]
  prod .F₀ (a , b) = M .-⊗- F∘ Cat⟨ a , b ⟩
  prod .F₁ {x = x} {y = y} (na , nb) = M .-⊗- ▸ nat where
    nat : Cat⟨ x .fst , x .snd ⟩ => Cat⟨ y .fst , y .snd ⟩
    nat .η x = (na .η x) , (nb .η x)
    nat .is-natural x y f i = (na .is-natural x y f i) , (nb .is-natural x y f i)
  prod .F-id = ext λ _ → M .-⊗- .F-id
  prod .F-∘ f g = ext λ _ → M .-⊗- .F-∘ _ _
  pw : Monoidal-category Cat[ C , D ]
  pw .-⊗- = prod
  pw .Unit = Const (M .Unit)
  pw .unitor-l = {! M .unitor-l  !}
  pw .unitor-r = {!   !}
  pw .associator = {!   !}
  pw .triangle = {!   !}
  pw .pentagon = {!   !}

what : (F : Functor C D) → (mon : Monoid-on Pointwise F) → (c : C .Ob) → Monoid-on M (F .F₀ c)
what F mon c .Monoid-on.η = {!   !}
what F mon c .Monoid-on.μ = {!   !}
what F mon c .Monoid-on.μ-unitl = {!   !}
what F mon c .Monoid-on.μ-unitr = {!   !}
what F mon c .Monoid-on.μ-assoc = {!   !}

MonCD→CMonD : Functor (∫ Mon[ Pointwise ]) (Cat[ C , ∫ Mon[ M ] ])
MonCD→CMonD .F₀ (F , mon) .F₀ c = F .F₀ c , {!   !}
MonCD→CMonD .F₀ (F , mon) .F₁ = {!   !}
MonCD→CMonD .F₀ (F , mon) .F-id = {!   !}
MonCD→CMonD .F₀ (F , mon) .F-∘ = {!   !}
MonCD→CMonD .F₁ = {!   !}
MonCD→CMonD .F-id = {!   !}
MonCD→CMonD .F-∘ = {!   !}

theorem : ∫ Mon[ Pointwise ] ≡ Cat[ C , ∫ Mon[ M ] ]
theorem = Precategory-path MonCD→CMonD {!   !}
