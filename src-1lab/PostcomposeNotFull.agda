open import Cat.Instances.Shape.Involution
open import Cat.Instances.Shape.Interval
open import Cat.Functor.Properties
open import Cat.Functor.Compose
open import Cat.Prelude

open import Data.Bool

open Precategory
open Functor
open _=>_

module PostcomposeNotFull where

{-
We prove that it is NOT the case that, for every full functor p, the
postcomposition functor p ∘ — is full.
-}

claim =
  ∀ {o ℓ o' ℓ' od ℓd} {C : Precategory o ℓ} {C' : Precategory o' ℓ'} {D : Precategory od ℓd}
  → (p : Functor C C') → is-full p → is-full (postcompose p {D = D})

module _ (assume : claim) where
  {-
  The counterexample consists of the following category (identities omitted):
    https://q.uiver.app/#q=WzAsMixbMCwwLCJhIl0sWzAsMSwiYiJdLFswLDBdLFsxLDEsIiIsMix7InJhZGl1cyI6LTN9XSxbMCwxLCIiLDAseyJjdXJ2ZSI6LTF9XSxbMCwxLCIiLDEseyJjdXJ2ZSI6MX1dXQ==
  where the loops on a and b are involutions, the involution on a swaps
  the two morphisms a ⇉ b, and the involution on b leaves them alone.
  There is a full functor p from C to the walking arrow that collapses
  all the morphisms, and there are two inclusion functors F and G from
  the walking involution into C. A natural transformation p ∘ F ⇒ p ∘ G
  is trivial, but a natural transformation F ⇒ G is a "ℤ/2ℤ-equivariant"
  morphism a → b, that is one that commutes with the involutions on a and b.
  There is no such thing in C, hence the action of p ∘ — on natural
  transformations (whiskering) cannot be surjective.
  -}

  C : Precategory lzero lzero
  C .Ob = Bool
  C .Hom true true = Bool
  C .Hom true false = Bool
  C .Hom false true = ⊥
  C .Hom false false = Bool
  C .Hom-set true true = hlevel 2
  C .Hom-set true false = hlevel 2
  C .Hom-set false true = hlevel 2
  C .Hom-set false false = hlevel 2
  C .id {true} = false
  C .id {false} = false
  C ._∘_ {true} {true} {true} = xor
  C ._∘_ {false} {false} {false} = xor
  C ._∘_ {true} {true} {false} f g = xor g f
  C ._∘_ {true} {false} {false} f g = g
  C .idr {true} {true} f = xor-falser f
  C .idr {true} {false} f = refl
  C .idr {false} {false} f = xor-falser f
  C .idl {true} {true} f = refl
  C .idl {true} {false} f = refl
  C .idl {false} {false} f = refl
  C .assoc {true} {true} {true} {true} f g h = xor-associative f g h
  C .assoc {false} {false} {false} {false} f g h = xor-associative f g h
  C .assoc {true} {true} {true} {false} f true true = sym (not-involutive f)
  C .assoc {true} {true} {true} {false} f true false = refl
  C .assoc {true} {true} {true} {false} f false h = refl
  C .assoc {true} {true} {false} {false} f g h = refl
  C .assoc {true} {false} {false} {false} f g h = refl

  p : Functor C (0≤1 ^op)
  p .F₀ o = o
  p .F₁ {true} {true} = _
  p .F₁ {true} {false} = _
  p .F₁ {false} {true} ()
  p .F₁ {false} {false} = _
  p .F-id {true} = refl
  p .F-id {false} = refl
  p .F-∘ {true} {true} {true} f g = refl
  p .F-∘ {true} {true} {false} f g = refl
  p .F-∘ {true} {false} {false} f g = refl
  p .F-∘ {false} {false} {false} f g = refl

  p-is-full : is-full p
  p-is-full {true} {true} _ = inc (false , refl)
  p-is-full {true} {false} _ = inc (false , refl)
  p-is-full {false} {false} _ = inc (false , refl)

  p*-is-full : is-full (postcompose p {D = ∙⤮∙})
  p*-is-full = assume p p-is-full

  F G : Functor ∙⤮∙ C
  F .F₀ _ = true
  F .F₁ f = f
  F .F-id = refl
  F .F-∘ _ _ = refl
  G .F₀ _ = false
  G .F₁ f = f
  G .F-id = refl
  G .F-∘ _ _ = refl

  impossible : F => G → ⊥
  impossible θ = not-no-fixed (sym (θ .is-natural _ _ true))

  pθ : p F∘ F => p F∘ G
  pθ .η = _
  pθ .is-natural _ _ _ = refl

  θ : ∥ F => G ∥
  θ = fst <$> p*-is-full pθ

  contradiction : ⊥
  contradiction = ∥-∥-rec! impossible θ
