```agda
open import 1Lab.Path.Cartesian
open import 1Lab.Path.Reasoning
open import 1Lab.Prelude

open import Algebra.Group.Concrete.Abelian
open import Algebra.Group.Concrete

open import Data.Set.Truncation
open import Data.Bool
open import Data.Int
open import Data.Nat
open import Data.Sum

open import Homotopy.Space.Suspension.Properties
open import Homotopy.Connectedness.Automation
open import Homotopy.Space.Suspension
open import Homotopy.Connectedness
open import Homotopy.Space.Circle
open import Homotopy.Space.Sphere
open import Homotopy.Base

open import Meta.Idiom
```

A formalisation of the first part of [The tangent bundles of spheres](https://www.youtube.com/watch?v=9T9B9XBjVpk)
by David Jaz Myers, Ulrik Buchholtz, Dan Christensen and Egbert Rijke, up until
the proof of the hairy ball theorem (except I don't have enough homotopy theory
to conclude that n-1 must be odd from `flipΣⁿ ≡ id`).

```agda
module TangentBundlesOfSpheres where

record Functorial (M : Effect) : Typeω where
  private module M = Effect M
  field
    ⦃ Map-Functorial ⦄ : Map M
    map-id : ∀ {ℓ} {A : Type ℓ} → map {M} {A = A} id ≡ id
    map-∘
      : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
      → {f : B → C} {g : A → B}
      → map {M} (f ∘ g) ≡ map f ∘ map g

  map-iso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    → (e : A ≃ B) → is-iso (map (Equiv.to e))
  map-iso e .is-iso.from = map (Equiv.from e)
  map-iso e .is-iso.rinv mb =
    map (Equiv.to e) (map (Equiv.from e) mb) ≡˘⟨ map-∘ $ₚ mb ⟩
    map ⌜ Equiv.to e ∘ Equiv.from e ⌝ mb     ≡⟨ ap! (funext (Equiv.ε e)) ⟩
    map id mb                                ≡⟨ map-id $ₚ mb ⟩
    mb                                       ∎
  map-iso e .is-iso.linv ma =
    map (Equiv.from e) (map (Equiv.to e) ma) ≡˘⟨ map-∘ $ₚ ma ⟩
    map ⌜ Equiv.from e ∘ Equiv.to e ⌝ ma     ≡⟨ ap! (funext (Equiv.η e)) ⟩
    map id ma                                ≡⟨ map-id $ₚ ma ⟩
    ma                                       ∎

  map≃
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    → (e : A ≃ B) → M.₀ A ≃ M.₀ B
  map≃ e = _ , is-iso→is-equiv (map-iso e)

  map-transport
    : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ}
    → (p : A ≡ B) → map (transport p) ≡ transport (ap M.₀ p)
  map-transport {A = A} p i = comp (λ i → M.₀ A → M.₀ (p i)) (∂ i) λ where
    j (j = i0) → map-id i
    j (i = i0) → map (funextP (transport-filler p) j)
    j (i = i1) → funextP (transport-filler (ap M.₀ p)) j

open Functorial ⦃ ... ⦄

is-natural
  : ∀ {M N : Effect} (let module M = Effect M; module N = Effect N) ⦃ _ : Map M ⦄ ⦃ _ : Map N ⦄
  → (f : ∀ {ℓ} {A : Type ℓ} → M.₀ A → N.₀ A) → Typeω
is-natural f =
  ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {g : A → B}
  → ∀ a → map g (f a) ≡ f (map g a)

-- Operations on suspensions: functorial action, flipping

instance
  Map-Susp : Map (eff Susp)
  Map-Susp .Map.map f N = N
  Map-Susp .Map.map f S = S
  Map-Susp .Map.map f (merid a i) = merid (f a) i

  Functorial-Susp : Functorial (eff Susp)
  Functorial-Susp .Functorial.Map-Functorial = Map-Susp
  Functorial-Susp .Functorial.map-id = funext $ Susp-elim _ refl refl λ _ _ → refl
  Functorial-Susp .Functorial.map-∘ = funext $ Susp-elim _ refl refl λ _ _ → refl

flipΣ : ∀ {ℓ} {A : Type ℓ} → Susp A → Susp A
flipΣ N = S
flipΣ S = N
flipΣ (merid a i) = merid a (~ i)

flipΣ∙ : ∀ {n} → Sⁿ (suc n) →∙ Sⁿ (suc n)
flipΣ∙ = flipΣ , sym (merid N)

flipΣ-involutive : ∀ {ℓ} {A : Type ℓ} → (p : Susp A) → flipΣ (flipΣ p) ≡ p
flipΣ-involutive = Susp-elim _ refl refl λ _ _ → refl

flipΣ≃ : ∀ {ℓ} {A : Type ℓ} → Susp A ≃ Susp A
flipΣ≃ = flipΣ , is-involutive→is-equiv flipΣ-involutive

flipΣ-natural : is-natural flipΣ
flipΣ-natural = Susp-elim _ refl refl λ _ _ → refl

twist : ∀ {ℓ} {A : Type ℓ} {a b : A} {p q : a ≡ b} (α : p ≡ q)
  → PathP (λ i → PathP (λ j → α i j ≡ α j (~ i))
                       (λ k → p (~ i ∧ k))
                       (λ k → q (~ i ∨ ~ k)))
          (λ j k → p (j ∨ k))
          (λ j k → q (j ∧ ~ k))
twist α i j k = hcomp (∂ i ∨ ∂ j ∨ ∂ k) λ where
  l (l = i0) → α (I-interp k i j) (I-interp k j (~ i))
  l (i = i0) → α (~ l ∧ k ∧ j) (k ∨ j)
  l (i = i1) → α (l ∨ ~ k ∨ j) (~ k ∧ j)
  l (j = i0) → α (~ l ∧ ~ k ∧ i) (k ∧ ~ i)
  l (j = i1) → α (l ∨ k ∨ i) (~ k ∨ ~ i)
  l (k = i0) → α i j
  l (k = i1) → α j (~ i)

-- Flipping ΣΣA along the first axis is homotopic to flipping along the second axis,
-- by rotating 180°.
rotateΣ : ∀ {ℓ} {A : Type ℓ} → map flipΣ ≡ flipΣ {A = Susp A}
rotateΣ = funext $ Susp-elim _ (merid N) (sym (merid S)) (
  Susp-elim _ (flip₁ (double-connection _ _)) (double-connection _ _)
    λ a i j k → hcomp (∂ j ∨ ∂ k) λ where
      l (l = i0) → merid (merid a j) i
      l (j = i0) → merid N (I-interp l i k)
      l (j = i1) → merid S (I-interp l i (~ k))
      l (k = i0) → twist (λ i j → merid (merid a i) j) (~ i) j (~ l)
      l (k = i1) → twist (λ i j → merid (merid a i) j) j i l)

Susp-ua→
  : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : Type ℓ'}
  → {e : A ≃ B} {f : Susp A → C} {g : Susp B → C}
  → (∀ sa → f sa ≡ g (map (e .fst) sa))
  → PathP (λ i → Susp (ua e i) → C) f g
Susp-ua→ h i N = h N i
Susp-ua→ h i S = h S i
Susp-ua→ {g = g} h i (merid a j) = hcomp (∂ i ∨ ∂ j) λ where
  k (k = i0) → g (merid (unglue a) j)
  k (i = i0) → h (merid a j) (~ k)
  k (i = i1) → g (merid a j)
  k (j = i0) → h N (i ∨ ~ k)
  k (j = i1) → h S (i ∨ ~ k)

-- The tangent bundles of spheres

Tⁿ⁻¹ : ∀ n → Sⁿ⁻¹ n → Type
θⁿ⁻¹ : ∀ n → (p : Sⁿ⁻¹ n) → Susp (Tⁿ⁻¹ n p) ≃ Sⁿ⁻¹ n

Tⁿ⁻¹ zero ()
Tⁿ⁻¹ (suc n) = Susp-elim _
  (Sⁿ⁻¹ n)
  (Sⁿ⁻¹ n)
  λ p → ua (θⁿ⁻¹ n p e⁻¹ ∙e flipΣ≃ ∙e θⁿ⁻¹ n p)

θⁿ⁻¹ zero ()
θⁿ⁻¹ (suc n) = Susp-elim _
  id≃
  flipΣ≃
  λ p → Σ-prop-pathp! $ Susp-ua→ $ happly $ sym $
    let module θ = Equiv (θⁿ⁻¹ n p) in
    flipΣ ∘ map (θ.to ∘ flipΣ ∘ θ.from)       ≡⟨ flipΣ ∘⟨ map-∘ ⟩
    flipΣ ∘ map θ.to ∘ map (flipΣ ∘ θ.from)   ≡⟨ flipΣ ∘ map _ ∘⟨ map-∘ ⟩
    flipΣ ∘ map θ.to ∘ map flipΣ ∘ map θ.from ≡⟨ flipΣ ∘ map _ ∘⟨ rotateΣ ⟩∘ map _ ⟩
    flipΣ ∘ map θ.to ∘ flipΣ ∘ map θ.from     ≡⟨ flipΣ ∘⟨ funext flipΣ-natural ⟩∘ map _ ⟩
    flipΣ ∘ flipΣ ∘ map θ.to ∘ map θ.from     ≡⟨ funext flipΣ-involutive ⟩∘⟨refl ⟩
    map θ.to ∘ map θ.from                     ≡⟨ funext (is-iso.rinv (map-iso (θⁿ⁻¹ n p))) ⟩
    id                                        ∎

antipodeⁿ⁻¹ : ∀ n → Sⁿ⁻¹ n ≃ Sⁿ⁻¹ n
antipodeⁿ⁻¹ zero = id≃
antipodeⁿ⁻¹ (suc n) = map≃ (antipodeⁿ⁻¹ n) ∙e flipΣ≃

θN : ∀ n → (p : Sⁿ⁻¹ n) → θⁿ⁻¹ n p .fst N ≡ p
θN (suc n) = Susp-elim _ refl refl λ p → transpose $
    ap sym (∙-idl _ ∙ ∙-idl _ ∙ ∙-elimr (∙-idl _ ∙ ∙-idl _ ∙ ∙-idr _ ∙ ∙-idl _ ∙ ∙-idl _ ∙ ∙-idl _))
  ∙ ap merid (θN n p)

θS : ∀ n → (p : Sⁿ⁻¹ n) → θⁿ⁻¹ n p .fst S ≡ Equiv.to (antipodeⁿ⁻¹ n) p
θS (suc n) = Susp-elim _ refl refl λ p → transpose $
    ap sym (∙-idl _ ∙ ∙-idl _ ∙ ∙-elimr (∙-idl _ ∙ ∙-idl _ ∙ ∙-idr _ ∙ ∙-idl _ ∙ ∙-idl _ ∙ ∙-idl _))
  ∙ ap (sym ∘ merid) (θS n p)

cⁿ⁻¹ : ∀ n → (p : Sⁿ⁻¹ n) → Tⁿ⁻¹ n p → p ≡ Equiv.to (antipodeⁿ⁻¹ n) p
cⁿ⁻¹ n p t = sym (θN n p) ∙ ap (θⁿ⁻¹ n p .fst) (merid t) ∙ θS n p

flipΣⁿ : ∀ n → Sⁿ⁻¹ n → Sⁿ⁻¹ n
flipΣⁿ zero = id
flipΣⁿ (suc n) = if⁺ even-or-odd n then flipΣ else id

flipΣⁿ⁺² : ∀ n → map (map (flipΣⁿ n)) ≡ flipΣⁿ (suc (suc n))
flipΣⁿ⁺² zero = ap map map-id ∙ map-id
flipΣⁿ⁺² (suc n) with even-or-odd n
... | inl e = ap map rotateΣ ∙ rotateΣ
... | inr o = ap map map-id ∙ map-id

antipode≡flip : ∀ n → Equiv.to (antipodeⁿ⁻¹ n) ≡ flipΣⁿ n
antipode≡flip zero = refl
antipode≡flip (suc zero) = ap (flipΣ ∘_) map-id
antipode≡flip (suc (suc n)) =
  flipΣ ∘ map (flipΣ ∘ map (antipodeⁿ⁻¹ n .fst))     ≡⟨ flipΣ ∘⟨ map-∘ ⟩
  flipΣ ∘ map flipΣ ∘ map (map (antipodeⁿ⁻¹ n .fst)) ≡⟨ flipΣ ∘⟨ rotateΣ ⟩∘ map _ ⟩
  flipΣ ∘ flipΣ ∘ map (map (antipodeⁿ⁻¹ n .fst))     ≡⟨ funext flipΣ-involutive ⟩∘⟨refl ⟩
  map (map (antipodeⁿ⁻¹ n .fst))                     ≡⟨ ap (map ∘ map) (antipode≡flip n) ⟩
  map (map (flipΣⁿ n))                               ≡⟨ flipΣⁿ⁺² n ⟩
  flipΣⁿ (suc (suc n))                               ∎

-- If the tangent bundle of the n-sphere admits a section for even n, then we get
-- a homotopy between flipΣ and the identity.
section→homotopy : ∀ n → ((p : Sⁿ⁻¹ n) → Tⁿ⁻¹ n p) → flipΣⁿ n ≡ id
section→homotopy n sec = sym $ funext (λ p → cⁿ⁻¹ n p (sec p)) ∙ antipode≡flip n

-- Now to prove that this in turn implies that n-1 is odd requires a bit of
-- homotopy theory in order to define the degrees of (unpointed!) maps of spheres.

degree∙ : ∀ n → (Sⁿ (suc n) →∙ Sⁿ (suc n)) → Int
degree∙ zero f = ΩS¹≃Int .fst (ap (transport SuspS⁰≡S¹) (Ωⁿ≃Sⁿ-map 1 .fst f))
degree∙ (suc n) = {! πₙ(Sⁿ) ≃ ℤ !}

degree∙-map : ∀ n f → degree∙ (suc n) (map (f .fst) , refl) ≡ degree∙ n f
degree∙-map n f = {! the isomorphisms above should be compatible with suspension !}

degree∙-id : ∀ n → degree∙ n id∙ ≡ 1
degree∙-id zero = refl
degree∙-id (suc n) = ap (degree∙ (suc n)) p ∙∙ degree∙-map n id∙ ∙∙ degree∙-id n
  where
    p : id∙ ≡ (map id , refl)
    p = Σ-pathp (sym map-id) refl

degree∙-flipΣ : ∀ n → degree∙ n flipΣ∙ ≡ -1
degree∙-flipΣ zero = refl -- neat.
degree∙-flipΣ (suc n) = ap (degree∙ (suc n)) p ∙∙ degree∙-map n flipΣ∙ ∙∙ degree∙-flipΣ n
  where
    p : flipΣ∙ ≡ (map flipΣ , refl)
    p = Σ-pathp (sym rotateΣ) (λ i j → merid N (~ i ∧ ~ j))

-- In order to define degrees of unpointed maps, we show that the function that
-- forgets the pointing of a map Sⁿ →∙ Sⁿ is a bijection (up to homotopy).
-- For n = 1, this is due to the fact that S¹ is the delooping of an abelian
-- group; for n > 1, we can use the fact that the n-sphere is simply connected.
Sⁿ-class-injective
  : ∀ n f → (p q : f N ≡ N)
  → ∥ Path (Sⁿ (suc n) →∙ Sⁿ (suc n)) (f , p) (f , q) ∥
Sⁿ-class-injective zero f p q = inc (S¹-cohomology.injective refl)
  where
    open ConcreteGroup
    Sⁿ⁼¹-concrete : ConcreteGroup lzero
    Sⁿ⁼¹-concrete .B = Sⁿ 1
    Sⁿ⁼¹-concrete .has-is-connected = is-connected→is-connected∙ (Sⁿ⁻¹-is-connected 2)
    Sⁿ⁼¹-concrete .has-is-groupoid = subst is-groupoid (sym SuspS⁰≡S¹) S¹-is-groupoid

    Sⁿ⁼¹≡S¹ : Sⁿ⁼¹-concrete ≡ S¹-concrete
    Sⁿ⁼¹≡S¹ = ConcreteGroup-path (Σ-path SuspS⁰≡S¹ refl)

    Sⁿ⁼¹-ab : is-concrete-abelian Sⁿ⁼¹-concrete
    Sⁿ⁼¹-ab = subst is-concrete-abelian (sym Sⁿ⁼¹≡S¹) S¹-concrete-abelian

    module S¹-cohomology = Equiv
      (first-concrete-abelian-group-cohomology
        Sⁿ⁼¹-concrete Sⁿ⁼¹-concrete Sⁿ⁼¹-ab)
Sⁿ-class-injective (suc n) f p q = ap (f ,_) <$> simply-connected p q

Sⁿ-class
  : ∀ n
  → ∥ (Sⁿ (suc n) →∙ Sⁿ (suc n)) ∥₀
  → ∥ (⌞ Sⁿ (suc n) ⌟ → ⌞ Sⁿ (suc n) ⌟) ∥₀
Sⁿ-class n = ∥-∥₀-rec (hlevel 2) λ (f , _) → inc f

Sⁿ-pointed≃unpointed
  : ∀ n
  → ∥ (Sⁿ (suc n) →∙ Sⁿ (suc n)) ∥₀
  ≃ ∥ (⌞ Sⁿ (suc n) ⌟ → ⌞ Sⁿ (suc n) ⌟) ∥₀
Sⁿ-pointed≃unpointed n .fst = Sⁿ-class n
Sⁿ-pointed≃unpointed n .snd = injective-surjective→is-equiv! (inj _ _) surj
  where
    inj : ∀ f g → Sⁿ-class n f ≡ Sⁿ-class n g → f ≡ g
    inj = elim! λ f ptf g ptg f≡g →
      ∥-∥₀-path.from do
        f≡g ← ∥-∥₀-path.to f≡g
        J (λ g _ → ∀ ptg → ∥ (f , ptf) ≡ (g , ptg) ∥)
          (Sⁿ-class-injective n f ptf)
          f≡g ptg

    surj : is-surjective (Sⁿ-class n)
    surj = ∥-∥₀-elim (λ _ → hlevel 2) λ f → do
      pointed ← connected (f N) N
      pure (inc (f , pointed) , refl)

degree : ∀ n → (⌞ Sⁿ (suc n) ⌟ → ⌞ Sⁿ (suc n) ⌟) → Int
degree n f = ∥-∥₀-rec (hlevel 2)
  (degree∙ n)
  (Equiv.from (Sⁿ-pointed≃unpointed n) (inc f))

degree∙≡degree : ∀ n f∙ → degree n (f∙ .fst) ≡ degree∙ n f∙
degree∙≡degree n f∙ = ap (∥-∥₀-rec _ _)
  (U.injective₂ {x = U.from (inc (f∙ .fst))} {y = inc f∙} (U.ε _) refl)
  where module U = Equiv (Sⁿ-pointed≃unpointed n)

flip≠id : ∀ n → ¬ flipΣ ≡ id {A = Sⁿ⁻¹ (suc n)}
flip≠id zero h = subst (Susp-elim _ ⊤ ⊥ (λ ())) (h $ₚ S) _
flip≠id (suc n) h = negsuc≠pos $
  -1               ≡˘⟨ degree∙-flipΣ n ⟩
  degree∙ n flipΣ∙ ≡˘⟨ degree∙≡degree n _ ⟩
  degree n flipΣ   ≡⟨ ap (degree n) h ⟩
  degree n id      ≡⟨ degree∙≡degree n _ ⟩
  degree∙ n id∙    ≡⟨ degree∙-id n ⟩
  1                ∎

hairy-ball : ∀ n → ((p : Sⁿ⁻¹ n) → Tⁿ⁻¹ n p) → is-even n
hairy-ball zero sec = ∣-zero
hairy-ball (suc n) sec with even-or-odd n | section→homotopy (suc n) sec
... | inl e | h = absurd (flip≠id n h)
... | inr o | _ = o
```
