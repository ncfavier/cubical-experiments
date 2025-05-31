```agda
open import 1Lab.Reflection.Regularity
open import 1Lab.Path.Cartesian
open import 1Lab.Reflection hiding (absurd)

open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Equivalence
open import Cat.Prelude hiding (_[_↦_])

open import Data.Fin
```

A synthetic account of categorical duality, based on an idea by [**David Wärn**](https://dwarn.se/).

The theory of categories has a fundamental S₂-symmetry that swaps "source"
and "target", which can be expressed synthetically by defining categories
in the context of the delooping BS₂.
By choosing as our delooping the type of 2-element types, this amounts
to defining categories relative to an arbitrary 2-element type X, which
we can think of as the set {source, target} except we've forgotten
which is which.
Then, instantiating this with a chosen 2-element type recovers usual
categories, and the non-trivial symmetry of BS₂ automatically gives
a symmetry of the type of categories which coincides with the usual
categorical opposite.

```agda
module SyntheticCategoricalDuality where
```

<details><summary>Some auxiliary definitions</summary>

```agda
private variable
  ℓ o h : Level
  X O : Type ℓ
  H : O → Type ℓ
  a b c : O
  i j k : X

excluded-middle : ∀ {x y z : Bool} → x ≠ y → y ≠ z → x ≡ z
excluded-middle {true} {y} {true} x≠y y≠z = refl
excluded-middle {true} {y} {false} x≠y y≠z = absurd (x≠y (sym (x≠false→x≡true y y≠z)))
excluded-middle {false} {y} {true} x≠y y≠z = absurd (x≠y (sym (x≠true→x≡false y y≠z)))
excluded-middle {false} {y} {false} x≠y y≠z = refl

instance
  Extensional-Bool-map
    : ∀ {ℓ ℓr} {C : Bool → Type ℓ} → ⦃ e : ∀ {b} → Extensional (C b) ℓr ⦄
    → Extensional ((b : Bool) → C b) ℓr
  Extensional-Bool-map ⦃ e ⦄ .Pathᵉ f g =
    e .Pathᵉ (f false) (g false) × e .Pathᵉ (f true) (g true)
  Extensional-Bool-map ⦃ e ⦄ .reflᵉ f =
    e .reflᵉ (f false) , e .reflᵉ (f true)
  Extensional-Bool-map ⦃ e ⦄ .idsᵉ .to-path (false≡ , true≡) = funext λ where
    true → e .idsᵉ .to-path true≡
    false → e .idsᵉ .to-path false≡
  Extensional-Bool-map ⦃ e ⦄ .idsᵉ .to-path-over (false≡ , true≡) =
    Σ-pathp (e .idsᵉ .to-path-over false≡) (e .idsᵉ .to-path-over true≡)

  Extensional-Bool-homotopy
    : ∀ {ℓ ℓr} {C : Bool → Type ℓ} → ⦃ e : ∀ {b} {x y : C b} → Extensional (x ≡ y) ℓr ⦄
    → {f g : (b : Bool) → C b}
    → Extensional (f ≡ g) ℓr
  Extensional-Bool-homotopy ⦃ e ⦄ {f} {g} .Pathᵉ p q =
    e .Pathᵉ (p $ₚ false) (q $ₚ false) × e .Pathᵉ (p $ₚ true) (q $ₚ true)
  Extensional-Bool-homotopy ⦃ e ⦄ .reflᵉ p =
    e .reflᵉ (p $ₚ false) , e .reflᵉ (p $ₚ true)
  Extensional-Bool-homotopy ⦃ e ⦄ .idsᵉ .to-path (false≡ , true≡) = funext-square λ where
    true → e .idsᵉ .to-path true≡
    false → e .idsᵉ .to-path false≡
  Extensional-Bool-homotopy ⦃ e ⦄ .idsᵉ .to-path-over (false≡ , true≡) =
    Σ-pathp (e .idsᵉ .to-path-over false≡) (e .idsᵉ .to-path-over true≡)

Bool-η : (b : Bool → O) → if (b true) (b false) ≡ b
Bool-η b = ext (refl , refl)
```
</details>

```agda
-- We define X-(pre)categories relative to a 2-element type X.
module X (o h : Level) (X : Type) (e : ∥ X ≃ Bool ∥) where
```

<details><summary>Some more auxiliary definitions</summary>

```agda
  private instance
    Finite-X : Finite X
    Finite-X = ⦇ Equiv→listing (e <&> _e⁻¹) auto ⦈

    Discrete-X : Discrete X
    Discrete-X = Finite→Discrete

    H-Level-X : H-Level X 2
    H-Level-X = Finite→H-Level

  _[_↦_] : (X → O) → X → O → X → O
  _[_↦_] b x m i = ifᵈ i ≡? x then m else b i

  assign-id : (b : X → O) → (x : X) → b [ x ↦ b x ] ≡ b
  assign-id b x = ext go where
    go : ∀ i → (b [ x ↦ b x ]) i ≡ b i
    go i with i ≡? x
    ... | yes p = ap b (sym p)
    ... | no _ = refl

  assign-const : (b : X → O) (i j : X) → j ≠ i → b [ j ↦ b i ] ≡ λ _ → b i
  assign-const b i j j≠i = ext go where
    go : ∀ k → (b [ j ↦ b i ]) k ≡ b i
    go k with k ≡? j
    ... | yes _ = refl
    ... | no k≠j = ap b $ ∥-∥-out! do
      e ← e
      pure (subst (λ X → {x y z : X} → x ≠ y → y ≠ z → x ≡ z)
         (ua (e e⁻¹)) excluded-middle k≠j j≠i)

  degenerate
    : (H : (X → O) → Type h) (b : X → O) (x : X) (f : H b) (id : H (λ _ → b x)) (i : X)
    → H (b [ i ↦ b x ])
  -- degenerate H b x f id i with i ≡ᵢ? x
  -- ... | yes reflᵢ = subst H (sym (assign-id b x)) f
  -- ... | no i≠x = subst H (sym (assign-const b x i (i≠x ⊙ Id≃path.from))) id
  -- NOTE performing the with-translation manually somehow results in fewer transports when X = Bool and x = i.
  -- I'm not sure what's happening here...
  degenerate H b x f id i = go (i ≡ᵢ? x) where
    go : Dec (i ≡ᵢ x) → H (b [ i ↦ b x ])
    go (yes reflᵢ) = subst H (sym (assign-id b x)) f
    go (no i≠x) = subst H (sym (assign-const b x i (i≠x ⊙ Id≃path.from))) id
```
</details>

```agda
  record XPrecategory : Type (lsuc (o ⊔ h)) where
    no-eta-equality

    field
      Ob : Type o

      -- Hom is a family indexed over "X-pairs" of objects, or boundaries.
      Hom : (X → Ob) → Type h
      Hom-set : (b : X → Ob) → is-set (Hom b)

      -- The identity lives over the constant pair.
      id : ∀ {x} → Hom λ _ → x

      -- Composition takes an outer boundary b, a middle object and an
      -- X-pair of morphisms with the appropriate boundaries and returns
      -- a morphism with boundary b.
      compose : (b : X → Ob) (m : Ob) → ((x : X) → Hom (b [ x ↦ m ])) → Hom b

      -- We can (and must) state both unit laws at once: given a "direction" x : X
      -- and a morphism f with boundary b, we can form the X-pair {f, id}
      -- where id lies in the direction x from f, and ask that the
      -- composite equal f.
      compose-id
        : (b : X → Ob) (f : Hom b) (x : X)
        → compose b (b x) (degenerate Hom b x f id) ≡ f

      -- TODO: associativity
      -- assoc
      --   : (b : X → Ob) (m n : Ob) (x : X)
      --   → compose b m (λ i → {!   !}) ≡ compose b n {!   !}
```

<details><summary>Some lemmas about paths between X-precategories</summary>

```agda
  private
    hom-set : ∀ (C : XPrecategory) {b} → is-set (C .XPrecategory.Hom b)
    hom-set C = C .XPrecategory.Hom-set _

  instance
    hlevel-proj-xhom : hlevel-projection (quote XPrecategory.Hom)
    hlevel-proj-xhom .hlevel-projection.has-level = quote hom-set
    hlevel-proj-xhom .hlevel-projection.get-level _ = pure (lit (nat 2))
    hlevel-proj-xhom .hlevel-projection.get-argument (c v∷ _) = pure c
    hlevel-proj-xhom .hlevel-projection.get-argument _ = typeError []

  private unquoteDecl record-iso = declare-record-iso record-iso (quote XPrecategory)

  XPrecategory-path
    : ∀ {C D : XPrecategory} (let module C = XPrecategory C; module D = XPrecategory D)
    → (ob≡ : C.Ob ≡ D.Ob)
    → (hom≡ : PathP (λ i → (X → ob≡ i) → Type h) C.Hom D.Hom)
    → (id≡ : PathP (λ i → ∀ {x} → hom≡ i (λ _ → x)) C.id D.id)
    → (compose≡ : PathP (λ i → ∀ (b : X → ob≡ i) (m : ob≡ i) (f : ∀ x → hom≡ i (b [ x ↦ m ])) → hom≡ i b) C.compose D.compose)
    → C ≡ D
  XPrecategory-path ob≡ hom≡ id≡ compose≡ = Iso.injective record-iso
    $ Σ-pathp ob≡ $ Σ-pathp hom≡ $ Σ-pathp prop!
    $ Σ-pathp id≡ $ Σ-pathp compose≡ $ hlevel 0 .centre
```
</details>

```agda
open X using (XPrecategory; XPrecategory-path)

-- We recover categories by choosing a 2-element type X with designated
-- source and target elements. Here we pick the booleans with
-- the convention that true = source and false = target.
2Precategory : (o h : Level) → Type (lsuc (o ⊔ h))
2Precategory o h = XPrecategory o h Bool (inc id≃)

module _ {o h : Level} where
  module B = X o h Bool (inc id≃)

  Precategory→2Precategory : Precategory o h → 2Precategory o h
  Precategory→2Precategory C = C' where
    module C = Precategory C
    open XPrecategory
    C' : 2Precategory o h
    C' .Ob = C.Ob
    C' .Hom b = C.Hom (b true) (b false)
    C' .Hom-set b = C.Hom-set _ _
    C' .id = C.id
    C' .compose b m f = f true C.∘ f false
    C' .compose-id b f true = ap₂ C._∘_ (transport-refl f) (transport-refl C.id) ∙ C.idr f
    C' .compose-id b f false = ap₂ C._∘_ (transport-refl C.id) (transport-refl f) ∙ C.idl f
    -- C' .assoc = ?

  2Precategory→Precategory : 2Precategory o h → Precategory o h
  2Precategory→Precategory C' = C where
    module C' = XPrecategory C'
    open Precategory
    C : Precategory o h
    C .Ob = C'.Ob
    C .Hom a b = C'.Hom (if a b)
    C .Hom-set a b = C'.Hom-set _
    C .id = subst C'.Hom (ext (refl , refl)) C'.id
    C ._∘_ {a} {b} {c} f g = C'.compose (if a c) b λ where
      true → subst C'.Hom (ext (refl , refl)) f
      false → subst C'.Hom (ext (refl , refl)) g
    C .idr {x} {y} f =
      ap (C'.compose (if x y) x) (ext
        ( sym (subst-∙ C'.Hom _ _ C'.id)
          ∙ ap (λ p → subst C'.Hom p C'.id) (ext (∙-idr refl , ∙-idr refl))
        , ap (λ p → subst C'.Hom p f) (ext (refl , refl))))
      ∙ C'.compose-id (if x y) f true
    C .idl {x} {y} f =
      ap (C'.compose (if x y) y) (ext
        ( ap (λ p → subst C'.Hom p f) (ext (refl , refl))
        , sym (subst-∙ C'.Hom _ _ C'.id)
          ∙ ap (λ p → subst C'.Hom p C'.id) (ext (∙-idr refl , ∙-idr refl))))
      ∙ C'.compose-id (if x y) f false
    C .assoc = {!   !}

  Precategory→2Precategory-is-iso : is-iso Precategory→2Precategory
  Precategory→2Precategory-is-iso .is-iso.from = 2Precategory→Precategory
  Precategory→2Precategory-is-iso .is-iso.rinv C' = XPrecategory-path _ _ _ _
    refl
    (ext λ b → ap C'.Hom (Bool-η b))
    (funextP' λ {a} → to-pathp⁻ (ap (λ p → subst C'.Hom p C'.id) (ext (refl , refl))))
    (funextP λ b → funextP λ m → funext-dep-i1 λ f →
    let
      path : PathP (λ i → C'.Hom (Bool-η b i))
        (C'.compose (if (b true) (b false)) m λ x → coe1→0 (λ i → C'.Hom (Bool-η b i B.[ x ↦ m ])) (f x))
        (C'.compose b m f)
      path i = C'.compose (Bool-η b i) m
        λ x → coe1→i (λ i → C'.Hom (Bool-η b i B.[ x ↦ m ])) i (f x)
    in
      ap (C'.compose (if (b true) (b false)) m) (ext
        ( sym (subst-∙ C'.Hom _ _ (f false))
          ∙ ap (λ p → subst C'.Hom p (f false)) (ext (∙-idr refl , ∙-idr refl))
        , sym (subst-∙ C'.Hom _ _ (f true))
          ∙ ap (λ p → subst C'.Hom p (f true)) (ext (∙-idr refl , ∙-idr refl))))
      ◁ path)
    where module C' = XPrecategory C'
  Precategory→2Precategory-is-iso .is-iso.linv C = Precategory-path F (iso id-equiv id-equiv)
    where
      module C = Precategory C
      open Functor
      F : Functor (2Precategory→Precategory (Precategory→2Precategory C)) C
      F .F₀ o = o
      F .F₁ f = f
      F .F-id = transport-refl C.id
      F .F-∘ f g = ap₂ C._∘_ (transport-refl f) (transport-refl g)

  Precategory≃2Precategory : Precategory o h ≃ 2Precategory o h
  Precategory≃2Precategory = Iso→Equiv (Precategory→2Precategory , Precategory→2Precategory-is-iso)

  -- We get categorical duality from the action of the X-category construction
  -- on the non-trivial path Bool ≡ Bool, and we check that this agrees
  -- with the usual categorical duality.
  duality : 2Precategory o h ≡ 2Precategory o h
  duality = ap₂ (XPrecategory _ _) (ua not≃) prop!

  _^Xop : 2Precategory o h → 2Precategory o h
  _^Xop = transport duality

  dualities-agree
    : (C : Precategory o h)
    → Precategory→2Precategory C ^Xop ≡ Precategory→2Precategory (C ^op)
  dualities-agree C = XPrecategory-path _ _ _ _
    refl
    (ext λ b → ap₂ C.Hom (transport-refl _) (transport-refl _))
    Regularity.reduce!
    (to-pathp (ext λ b m f → Regularity.reduce!))
    where module C = Precategory C
```
