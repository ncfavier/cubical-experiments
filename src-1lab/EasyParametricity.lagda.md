<details>
<summary>Imports</summary>

```agda
open import Cat.Prelude renaming (J to J⁼)
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Discrete
open import Cat.Instances.Shape.Join
open import Cat.Instances.Product

open import Data.Sum

import Cat.Reasoning
import Cat.Functor.Reasoning
import Cat.Functor.Bifunctor

open Precategory
open Functor
open make-is-limit
```
</details>

This module formalises a very interesting result from Jem Lord's recent work on
[*Easy Parametricity*](https://hott-uf.github.io/2025/abstracts/HoTTUF_2025_paper_21.pdf),
presented at [HoTT/UF 2025](https://hott-uf.github.io/2025/).

```agda
module EasyParametricity {u} where

U = Type u
𝟘 = Lift u ⊥
𝟙 = Lift u ⊤

record Bridge {ℓ} (A : Type ℓ) (x y : A) : Type (ℓ ⊔ lsuc u) where
  no-eta-equality
  constructor bridge
  pattern
  field
    app  : U → A
    app𝟘 : app 𝟘 ≡ x
    app𝟙 : app 𝟙 ≡ y

ap-bridge : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) {x y : A} → Bridge A x y → Bridge B (f x) (f y)
ap-bridge f (bridge app app𝟘 app𝟙) = bridge (f ⊙ app) (ap f app𝟘) (ap f app𝟙)

postulate
  -- An immediate consequence of Jem Lord's parametricity axiom: a function
  -- out of U into a U-small type cannot tell 0 and 1 apart; this is all we need here.
  -- If we think of functions f : U → A as "bridges" from f 0 to f 1, then this
  -- basically says that U-small types are "bridge-discrete".
  -- parametricity : ∀ {A : U} (f : U → A) → f 𝟘 ≡ f 𝟙
  parametricity : ∀ {A : U} {x y : A} → Bridge A x y → x ≡ y

-- The type of formal composites r ∘ l : A → B in C. We want to think of this
-- as the type of factorisations of some morphism f : A → B, but it turns out
-- to be unnecessary to track f in the type.
record Factorisation {o ℓ} (C : Precategory o ℓ) (A B : C .Ob) : Type (o ⊔ ℓ) where
  constructor factor
  module C = Precategory C
  field
    X : C.Ob
    l : C.Hom A X
    r : C.Hom X B

module _
  {o ℓ} {C : Precategory o ℓ}
  (let module C = Precategory C)
  where

  module _ {A B : C.Ob} (f : C.Hom A B) where

    -- The two factorisations id ∘ f and f ∘ id.
    _∘id id∘_ : Factorisation C A B
    _∘id = factor A C.id f
    id∘_ = factor B f C.id

  module _
    (C-complete : is-complete u lzero C)
    (C-category : is-category C)
    {A B : C.Ob} (f : C.Hom A B)
    where

    -- We define a "bridge" in the type of factorisations from id ∘ f to f ∘ id.
    b : U → Factorisation C A B
    b P = fac (C-complete diagram) module b where

      -- This is the interesting part: given a type P : U, we construct the
      -- wide pullback of P-many copies of f.
      -- Since we only care about the cases where P is a proposition, we
      -- can just take the discrete or codiscrete category on P and adjoin a
      -- terminal object to get our diagram shape.
      J : Precategory u lzero
      J = Codisc' P ▹

      diagram : Functor J C
      diagram .F₀ (inl _) = A
      diagram .F₀ (inr _) = B
      diagram .F₁ {inl _} {inl _} _ = C.id
      diagram .F₁ {inl _} {inr _} _ = f
      diagram .F₁ {inr _} {inr _} _ = C.id
      diagram .F-id {inl _} = refl
      diagram .F-id {inr _} = refl
      diagram .F-∘ {inl _} {inl _} {inl _} _ _ = sym (C.idl _)
      diagram .F-∘ {inl _} {inl _} {inr _} _ _ = sym (C.idr _)
      diagram .F-∘ {inl _} {inr _} {inr _} _ _ = sym (C.idl _)
      diagram .F-∘ {inr _} {inr _} {inr _} _ _ = sym (C.idl _)

      -- Given a limit of this diagram (which exists by the assumption of U-completeness),
      -- we get a factorisation of f as the universal map followed by the projection to B.
      fac : Limit diagram → Factorisation C A B
      fac lim = factor X l r where
        module lim = Limit lim
        X : C.Ob
        X = lim.apex
        l : C.Hom A X
        l = lim.universal (λ { (inl _) → C.id; (inr _) → f }) λ where
          {inl _} {inl _} _ → C.idl _
          {inl _} {inr _} _ → C.idr _
          {inr _} {inr _} _ → C.idl _
        r : C.Hom X B
        r = lim.cone ._=>_.η (inr tt)

    -- We check that the endpoints of the bridge are what we expect: when P
    -- is empty, we are taking the limit of the single-object diagram B, so
    -- our factorisation is A → B → B.
    b0 : b 𝟘 ≡ id∘ f
    b0 = ap (b.fac 𝟘) (Limit-is-prop C-category (C-complete _) (to-limit lim)) where
      lim : is-limit (b.diagram 𝟘) B _
      lim = to-is-limit λ where
        .ψ (inr _) → C.id
        .commutes {inr _} {inr _} _ → C.idl _
        .universal eps comm → eps (inr _)
        .factors {inr _} eps comm → C.idl _
        .unique eps comm other fac → sym (C.idl _) ∙ fac (inr _)

    -- When P is contractible, we are taking the limit of the arrow diagram
    -- A → B, so our factorisation is A → A → B.
    b1 : b 𝟙 ≡ f ∘id
    b1 = ap (b.fac 𝟙) (Limit-is-prop C-category (C-complete _) (to-limit lim)) where
      lim : is-limit (b.diagram 𝟙) A _
      lim = to-is-limit λ where
        .ψ (inl _) → C.id
        .ψ (inr _) → f
        .commutes {inl _} {inl _} _ → C.idl _
        .commutes {inl _} {inr _} _ → C.idr _
        .commutes {inr _} {inr _} _ → C.idl _
        .universal eps comm → eps (inl (lift tt))
        .factors {inl _} eps comm → C.idl _
        .factors {inr _} eps comm → comm {inl _} {inr _} _
        .unique eps comm other fac → sym (C.idl _) ∙ fac (inl _)

    factorisation-bridge : Bridge _ (id∘ f) (f ∘id)
    factorisation-bridge = bridge b b0 b1

-- We prove theorem 1.a from Easy Parametricity: if C is a U-complete univalent category
-- and D is a locally U-small category, then naturality of transformations between
-- functors C → D is free.
module _
  {o o' ℓ} {C : Precategory o ℓ} {D : Precategory o' u}
  (let module C = Cat.Reasoning C) (let module D = Cat.Reasoning D)
  (C-complete : is-complete u lzero C)
  (C-category : is-category C)
  where

  module _
    (F G : Functor C D)
    (let module F = Cat.Functor.Reasoning F) (let module G = Cat.Functor.Reasoning G)
    (η : ∀ x → D.Hom (F.₀ x) (G.₀ x))
    where

    natural : is-natural-transformation F G η
    natural A B f = G.introl refl ∙ z0≡z1 ∙ (D.refl⟩∘⟨ F.elimr refl) where

      -- Given a factorisation A → X → B, we define the map
      --       F A
      --        ↓
      -- η X : F X → G X
      --              ↓
      --             G B
      -- which recovers the naturality square for f as the factorisation varies
      -- from id ∘ f to f ∘ id.
      z : Factorisation C A B → D.Hom (F.F₀ A) (G.F₀ B)
      z (factor X l r) = G.F₁ r D.∘ η X D.∘ F.F₁ l

      -- As a result, we get a bridge from one side of the naturality square
      -- to the other; since D is locally U-small, the Hom-sets of D are bridge-discrete,
      -- so we get the desired equality.
      z0≡z1 : z (id∘ f) ≡ z (f ∘id)
      z0≡z1 = parametricity (ap-bridge z (factorisation-bridge C-complete C-category f))

  module _
    (D-complete : is-complete (o ⊔ ℓ) (o ⊔ ℓ) D)
    (F G : Functor (C ^op ×ᶜ C) D)
    (let module F = Cat.Functor.Bifunctor F) (let module G = Cat.Functor.Bifunctor G)
    (η : ∀ x → D.Hom (F.₀ (x , x)) (G.₀ (x , x)))
    where

    dinatural
      : ∀ A B (f : C.Hom A B)
      → G.first f D.∘ η B D.∘ F.second f ≡ G.second f D.∘ η A D.∘ F.first f
    dinatural A B f = z0≡z1 where
      z : Factorisation C A B → D.Hom (F.F₀ (B , A)) (G.F₀ (A , B))
      z (factor X l r) = G.₁ (l , r) D.∘ η X D.∘ F.₁ (r , l)
      z0≡z1 : z (id∘ f) ≡ z (f ∘id)
      z0≡z1 = parametricity (ap-bridge z (factorisation-bridge C-complete C-category f))

    strong-dinatural
      : ∀ A B (f : C.Hom A B)
      → ∀ W (w0 : D.Hom W (F.₀ (A , A))) (w1 : D.Hom W (F.₀ (B , B)))
      → F.second f D.∘ w0 ≡ F.first f D.∘ w1
      → G.first f D.∘ η B D.∘ w1 ≡ G.second f D.∘ η A D.∘ w0
    strong-dinatural A B f = go where
      J : Precategory (o ⊔ ℓ) (o ⊔ ℓ)
      J = Disc (Factorisation C A B) {! C-category  !} ▹
      diagram : Functor J D
      diagram .F₀ (inl (factor X l r)) = F.₀ (X , X)
      diagram .F₀ (inr _) = F.₀ (A , B)
      diagram .F₁ {inl x} {inl y} (lift p) = subst (λ y → D.Hom (F.₀ (x .Factorisation.X , x .Factorisation.X)) (F.₀ (y .Factorisation.X , y .Factorisation.X))) p D.id
      diagram .F₁ {inl (factor X l r)} {inr _} f = F.₁ (l , r)
      diagram .F₁ {inr _} {inr _} f = D.id
      diagram .F-id {inl _} = transport-refl D.id
      diagram .F-id {inr _} = refl
      diagram .F-∘ {inl _} {inl _} {inl _} (lift p) (lift q) = {! subst-∙ (λ y → D.Hom (F.₀ ?) (F.₀ ?)) q p D.id !}
      diagram .F-∘ {inl _} {inl _} {inr _} f g = {!   !}
      diagram .F-∘ {inl _} {inr _} {inr _} f g = sym (D.idl _)
      diagram .F-∘ {inr _} {inr _} {inr _} f g = sym (D.idl _)
      pb : Limit diagram
      pb = D-complete diagram
      module pb = Limit pb
      W : D.Ob
      W = pb.apex
      w0 : D.Hom W (F.₀ (A , A))
      w0 = pb.cone ._=>_.η (inl (f ∘id))
      w1 : D.Hom W (F.₀ (B , B))
      w1 = pb.cone ._=>_.η (inl (id∘ f))
      z : Factorisation C A B → D.Hom W (G.F₀ (A , B))
      z (factor X l r) = G.₁ (l , r) D.∘ η X D.∘ pb.cone ._=>_.η (inl (factor X l r))
      goal : G.first f D.∘ η B D.∘ w1 ≡ G.second f D.∘ η A D.∘ w0
      goal = parametricity (ap-bridge z (factorisation-bridge C-complete C-category f))

      go
        : ∀ W (w0 : D.Hom W (F.₀ (A , A))) (w1 : D.Hom W (F.₀ (B , B)))
        → F.second f D.∘ w0 ≡ F.first f D.∘ w1
        → G.first f D.∘ η B D.∘ w1 ≡ G.second f D.∘ η A D.∘ w0
      go W w0 w1 comm = {!   !}

open import Cat.Instances.Sets.Complete
open import Cat.Instances.Sets
test : _
test = strong-dinatural {C = Sets u} {D = Sets u} (Sets-is-complete {u} {lzero} {lzero}) Sets-is-category {!   !}
```
