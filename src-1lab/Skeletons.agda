open import Cat.Functor.Base
open import Cat.Functor.Equivalence
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Properties
open import Cat.Instances.FinSets
open import Cat.Instances.Sets
open import Cat.Prelude
open import Cat.Skeletal
open import Data.Fin
open import Data.Nat

import Cat.Reasoning

open Functor
open is-precat-iso

{-
Formalising parts of https://math.stackexchange.com/a/4943344, with
finite-dimensional real vector spaces replaced with finite sets
(the situation is exactly the same).
-}
module Skeletons where

module Sets {ℓ} = Cat.Reasoning (Sets ℓ)

{-
In the role of the skeletal category whose objects are natural numbers
representing ℝⁿ and whose morphisms are matrices, we use the skeletal
category whose objects are natural numbers representing the standard
finite sets [n] and whose morphisms are functions.
-}
S : Precategory lzero lzero
S = FinSets

S-is-skeletal : is-skeletal S
S-is-skeletal = path-from-has-iso→is-skeletal _ $ rec! λ is →
  Fin-injective (iso→equiv (F-map-iso Fin→Sets is))

{-
In the role of the univalent category of finite-dimensional real vector
spaces, we use the univalent category of finite sets, here realised as
the *essential image* of the inclusion of S into sets.
Explicitly, an object of C is a set X such that there merely exists a
natural number n such that X ≃ [n].
Equivalently, an object of C is a set X equipped with a natural number
n such that ∥ X ≃ [n] ∥ (we can extract n from the truncation because
the statements X ≃ [n] are mutually exclusive for distinct n).
C is a Rezk completion of S.
-}
C : Precategory (lsuc lzero) lzero
C = Essential-image Fin→Sets

C-is-category : is-category C
C-is-category = Restrict-is-category _ (λ _ → hlevel 1) Sets-is-category

{-
Finally, if we remove the truncation (but do not change the morphisms),
we get a skeletal category *isomorphic* to S, because we can contract X
away. This is entirely analogous to the way that the naïve definition
of the image of a function using Σ instead of ∃ yields the domain of
the function (https://1lab.dev/1Lab.Counterexamples.Sigma.html).
-}
C' : Precategory (lsuc lzero) lzero
C' = Restrict {C = Sets _} λ X → Σ[ n ∈ Nat ] Fin→Sets .F₀ n Sets.≅ X

S→C' : Functor S C'
S→C' .F₀ n = el! (Fin n) , n , Sets.id-iso
S→C' .F₁ f = f
S→C' .F-id = refl
S→C' .F-∘ _ _ = refl

S≡C' : is-precat-iso S→C'
S≡C' .has-is-ff = id-equiv
S≡C' .has-is-iso = inverse-is-equiv (e .snd) where
  e : (Σ[ X ∈ Set lzero ] Σ[ n ∈ Nat ] Fin→Sets .F₀ n Sets.≅ X) ≃ Nat
  e = Σ-swap₂ ∙e Σ-contract λ n → is-contr-ΣR Sets-is-category

{-
Since C is a Rezk completion of S, we should expect to have a fully
faithful and essentially surjective functor S → C.
-}

S→C : Functor S C
S→C = Essential-inc Fin→Sets

S→C-is-ff : is-fully-faithful S→C
S→C-is-ff = ff→Essential-inc-ff Fin→Sets Fin→Sets-is-ff

S→C-is-eso : is-eso S→C
S→C-is-eso = Essential-inc-eso Fin→Sets

{-
However, this functor is *not* an equivalence of categories: in order
to obtain a functor going the other way, we would have to choose an
enumeration of every finite set in a coherent way. This is a form of
global choice, which is just false (https://1lab.dev/1Lab.Counterexamples.GlobalChoice.html).
TODO: prove this
-}
