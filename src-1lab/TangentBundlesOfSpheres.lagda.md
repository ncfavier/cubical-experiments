```agda
open import 1Lab.Path.Cartesian
open import 1Lab.Path.Reasoning
open import 1Lab.Prelude

open import Data.Int
open import Data.Nat
open import Data.Sum

open import Homotopy.Space.Sphere.Degree
open import Homotopy.Space.Suspension
open import Homotopy.Space.Sphere
open import Homotopy.Conjugation
open import Homotopy.Loopspace
open import Homotopy.Base
```

A formalisation of [The tangent bundles of spheres](https://www.youtube.com/watch?v=9T9B9XBjVpk)
by David Jaz Myers, Ulrik Buchholtz, Dan Christensen and Egbert Rijke, up until
the proof of the hairy ball theorem.

```agda
module TangentBundlesOfSpheres where

-- Some generalities about wild functors and natural transformations.

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
  Map-Susp .Map.map = Susp-map

  Functorial-Susp : Functorial (eff Susp)
  Functorial-Susp .Functorial.Map-Functorial = Map-Susp
  Functorial-Susp .Functorial.map-id = funext $ Susp-elim _ refl refl λ _ _ → refl
  Functorial-Susp .Functorial.map-∘ = funext $ Susp-elim _ refl refl λ _ _ → refl

flipΣ : ∀ {ℓ} {A : Type ℓ} → Susp A → Susp A
flipΣ north = south
flipΣ south = north
flipΣ (merid a i) = merid a (~ i)

flipΣ∙ : ∀ {n} → Sⁿ (suc n) →∙ Sⁿ (suc n)
flipΣ∙ = flipΣ , sym (merid north)

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
rotateΣ = funext $ Susp-elim _ (merid north) (sym (merid south)) (
  Susp-elim _ (flip₁ (double-connection _ _)) (double-connection _ _)
    λ a i j k → hcomp (∂ j ∨ ∂ k) λ where
      l (l = i0) → merid (merid a j) i
      l (j = i0) → merid north (I-interp l i k)
      l (j = i1) → merid south (I-interp l i (~ k))
      l (k = i0) → twist (λ i j → merid (merid a i) j) (~ i) j (~ l)
      l (k = i1) → twist (λ i j → merid (merid a i) j) j i l)

Susp-map∙-flipΣ∙ : ∀ n → flipΣ∙ {n = suc n} ≡ Susp-map∙ flipΣ∙
Susp-map∙-flipΣ∙ n = sym rotateΣ ,ₚ λ i j → merid north (~ i ∧ ~ j)

opaque
  unfolding Ωⁿ≃∙Sⁿ-map Ω¹-map conj

  degree∙-flipΣ : ∀ n → degree∙ n flipΣ∙ ≡ -1
  degree∙-flipΣ zero = refl
  degree∙-flipΣ (suc n) =
       ap (degree∙ (suc n)) (Susp-map∙-flipΣ∙ n)
    ∙∙ degree∙-Susp-map∙ n flipΣ∙
    ∙∙ degree∙-flipΣ n

flip≠id : ∀ n → ¬ flipΣ ≡ id {A = Sⁿ⁻¹ (suc n)}
flip≠id zero h = subst (Susp-elim _ ⊤ ⊥ (λ ())) (h $ₚ south) _
flip≠id (suc n) h = negsuc≠pos $
  -1               ≡˘⟨ degree∙-flipΣ n ⟩
  degree∙ n flipΣ∙ ≡˘⟨ degree≡degree∙ n _ ⟩
  degree n flipΣ   ≡⟨ ap (degree n) h ⟩
  degree n id      ≡⟨ degree≡degree∙ n _ ⟩
  degree∙ n id∙    ≡⟨ degree∙-id∙ n ⟩
  1                ∎

Susp-ua→
  : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : Type ℓ'}
  → {e : A ≃ B} {f : Susp A → C} {g : Susp B → C}
  → (∀ sa → f sa ≡ g (map (e .fst) sa))
  → PathP (λ i → Susp (ua e i) → C) f g
Susp-ua→ h i north = h north i
Susp-ua→ h i south = h south i
Susp-ua→ {g = g} h i (merid a j) = hcomp (∂ i ∨ ∂ j) λ where
  k (k = i0) → g (merid (unglue a) j)
  k (i = i0) → h (merid a j) (~ k)
  k (i = i1) → g (merid a j)
  k (j = i0) → h north (i ∨ ~ k)
  k (j = i1) → h south (i ∨ ~ k)

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

θN : ∀ n → (p : Sⁿ⁻¹ n) → θⁿ⁻¹ n p .fst north ≡ p
θN (suc n) = Susp-elim _ refl refl λ p → transpose $
    ap sym (∙-idl _ ∙ ∙-idl _ ∙ ∙-elimr (∙-idl _ ∙ ∙-idl _ ∙ ∙-idr _ ∙ ∙-idl _ ∙ ∙-idl _ ∙ ∙-idl _))
  ∙ ap merid (θN n p)

θS : ∀ n → (p : Sⁿ⁻¹ n) → θⁿ⁻¹ n p .fst south ≡ Equiv.to (antipodeⁿ⁻¹ n) p
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

-- If the tangent bundle of the n-sphere admits a section, then we get
-- a homotopy between flipΣⁿ and the identity.
section→homotopy : ∀ n → ((p : Sⁿ⁻¹ n) → Tⁿ⁻¹ n p) → flipΣⁿ n ≡ id
section→homotopy n sec = sym $ funext (λ p → cⁿ⁻¹ n p (sec p)) ∙ antipode≡flip n

-- Therefore, n must be even.
hairy-ball : ∀ n → ((p : Sⁿ⁻¹ n) → Tⁿ⁻¹ n p) → is-even n
hairy-ball zero sec = ∣-zero
hairy-ball (suc n) sec with even-or-odd n | section→homotopy (suc n) sec
... | inl e | h = absurd (flip≠id n h)
... | inr o | _ = o
```
