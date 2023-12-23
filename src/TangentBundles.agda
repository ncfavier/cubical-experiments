open import 1Lab.Path.Cartesian
open import 1Lab.Path.Reasoning
open import 1Lab.Prelude hiding (double-connection)

open import Data.Bool

open import Homotopy.Space.Suspension
open import Homotopy.Space.Sphere

open import Meta.Idiom

{-
A work-in-progress formalisation of the first part of https://www.youtube.com/watch?v=9T9B9XBjVpk
by David Jaz Myers, Ulrik Buchholtz, Dan Christensen and Egbert Rijke, up until
the proof of the hairy ball theorem (except I don't have enough homotopy theory yet
to conclude that n-1 must be odd from flipΣⁿ ≡ id).
-}
module TangentBundles where

id≃ : ∀ {ℓ} {A : Type ℓ} → A ≃ A
id≃ = id , id-equiv

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
  map-iso e .is-iso.inv = map (Equiv.from e)
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

flipΣ-involutive : ∀ {ℓ} {A : Type ℓ} → (p : Susp A) → flipΣ (flipΣ p) ≡ p
flipΣ-involutive = Susp-elim _ refl refl λ _ _ → refl

flipΣ≃ : ∀ {ℓ} {A : Type ℓ} → Susp A ≃ Susp A
flipΣ≃ = flipΣ , is-involutive→is-equiv flipΣ-involutive

flipΣ-natural : is-natural flipΣ
flipΣ-natural = Susp-elim _ refl refl λ _ _ → refl

double-connection
  : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → Square p p q q
double-connection {y = y} p q i j = hcomp (∂ i ∨ ∂ j) λ where
  k (k = i0) → y
  k (i = i0) → p (j ∨ ~ k)
  k (i = i1) → q (j ∧ k)
  k (j = i0) → p (i ∨ ~ k)
  k (j = i1) → q (i ∧ k)

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
  k (k = i0) → g (merid (unglue (∂ i) a) j)
  k (i = i0) → h (merid a j) (~ k)
  k (i = i1) → g (merid a j)
  k (j = i0) → h N (i ∨ ~ k)
  k (j = i1) → h S (i ∨ ~ k)

-- The tangent bundles of spheres

antipodeⁿ⁻¹ : (n : Nat) → Sⁿ⁻¹ n ≃ Sⁿ⁻¹ n
antipodeⁿ⁻¹ zero = id≃
antipodeⁿ⁻¹ (suc n) = map≃ (antipodeⁿ⁻¹ n) ∙e flipΣ≃

Tⁿ⁻¹ : (n : Nat) → Sⁿ⁻¹ n → Type
θⁿ⁻¹ : (n : Nat) → (p : Sⁿ⁻¹ n) → Susp (Tⁿ⁻¹ n p) ≃ Sⁿ⁻¹ n

Tⁿ⁻¹ zero ()
Tⁿ⁻¹ (suc n) = Susp-elim _
  (Sⁿ⁻¹ n)
  (Sⁿ⁻¹ n)
  λ p → ua (θⁿ⁻¹ n p e⁻¹ ∙e flipΣ≃ ∙e θⁿ⁻¹ n p)

θⁿ⁻¹ zero ()
θⁿ⁻¹ (suc n) = Susp-elim _
  id≃
  flipΣ≃
  λ p → Σ-prop-pathp hlevel! $ Susp-ua→ λ s →
    let module θ = Equiv (θⁿ⁻¹ n p) in sym $
    flipΣ (map (θ.to ∘ flipΣ ∘ θ.from) s)       ≡⟨ ap flipΣ (map-∘ $ₚ s) ⟩
    flipΣ (map θ.to (map (flipΣ ∘ θ.from) s))   ≡⟨ ap (flipΣ ∘ map θ.to) (map-∘ $ₚ s) ⟩
    flipΣ (map θ.to (map flipΣ (map θ.from s))) ≡⟨ ap (flipΣ ∘ map θ.to) (rotateΣ $ₚ map θ.from s) ⟩
    flipΣ (map θ.to (flipΣ (map θ.from s)))     ≡⟨ ap flipΣ (flipΣ-natural (map θ.from s)) ⟩
    flipΣ (flipΣ (map θ.to (map θ.from s)))     ≡⟨ flipΣ-involutive _ ⟩
    map θ.to (map θ.from s)                     ≡⟨ is-iso.rinv (map-iso (θⁿ⁻¹ n p)) s ⟩
    s                                           ∎

θN : (n : Nat) → (p : Sⁿ⁻¹ n) → θⁿ⁻¹ n p .fst N ≡ p
θN (suc n) = Susp-elim _ refl refl λ p → transpose $
    ap sym (∙-idl _ ∙ ∙-idl _ ∙ ∙-elimr (∙-idl _ ∙ ∙-idl _ ∙ ∙-idr _ ∙ ∙-idl _ ∙ ∙-idl _ ∙ ∙-idl _))
  ∙ ap merid (θN n p)

θS : (n : Nat) → (p : Sⁿ⁻¹ n) → θⁿ⁻¹ n p .fst S ≡ Equiv.to (antipodeⁿ⁻¹ n) p
θS (suc n) = Susp-elim _ refl refl λ p → transpose $
    ap sym (∙-idl _ ∙ ∙-idl _ ∙ ∙-elimr (∙-idl _ ∙ ∙-idl _ ∙ ∙-idr _ ∙ ∙-idl _ ∙ ∙-idl _ ∙ ∙-idl _))
  ∙ ap (sym ∘ merid) (θS n p)

cⁿ⁻¹ : (n : Nat) → (p : Sⁿ⁻¹ n) → Tⁿ⁻¹ n p → p ≡ Equiv.to (antipodeⁿ⁻¹ n) p
cⁿ⁻¹ n p t = sym (θN n p) ∙ ap (θⁿ⁻¹ n p .fst) (merid t) ∙ θS n p

even odd : Nat → Bool
even zero = true
even (suc n) = odd n
odd zero = false
odd (suc n) = even n

flipΣⁿ : (n : Nat) → Sⁿ⁻¹ n → Sⁿ⁻¹ n
flipΣⁿ zero = id
flipΣⁿ (suc n) = if even n then flipΣ else id

flipΣⁿ⁺² : (n : Nat) → map (map (flipΣⁿ n)) ≡ flipΣⁿ (suc (suc n))
flipΣⁿ⁺² zero = ap map map-id ∙ map-id
flipΣⁿ⁺² (suc n) with even n
... | true = ap map rotateΣ ∙ rotateΣ
... | false = ap map map-id ∙ map-id

antipode≡flip : (n : Nat) → Equiv.to (antipodeⁿ⁻¹ n) ≡ flipΣⁿ n
antipode≡flip zero = refl
antipode≡flip (suc zero) = ap (flipΣ ∘_) map-id
antipode≡flip (suc (suc zero)) = -- TODO can i avoid this case?
  flipΣ ∘ map (flipΣ ∘ map id)     ≡⟨ ap (flipΣ ∘_) map-∘ ⟩
  flipΣ ∘ map flipΣ ∘ map (map id) ≡⟨ ap (λ x → flipΣ ∘ x ∘ map (map id)) rotateΣ ⟩
  flipΣ ∘ flipΣ ∘ map (map id)     ≡⟨ funext (λ _ → flipΣ-involutive _) ⟩
  map (map id)                     ≡⟨ ap map map-id ⟩
  map id                           ≡⟨ map-id ⟩
  id                               ∎
antipode≡flip (suc (suc (suc n))) =
  flipΣ ∘ map (flipΣ ∘ map (antipodeⁿ⁻¹ (suc n) .fst))     ≡⟨ ap (flipΣ ∘_) map-∘ ⟩
  flipΣ ∘ map flipΣ ∘ map (map (antipodeⁿ⁻¹ (suc n) .fst)) ≡⟨ ap (λ x → flipΣ ∘ x ∘ map (map (antipodeⁿ⁻¹ (suc n) .fst))) rotateΣ ⟩
  flipΣ ∘ flipΣ ∘ map (map (antipodeⁿ⁻¹ (suc n) .fst))     ≡⟨ funext (λ _ → flipΣ-involutive _) ⟩
  map (map (antipodeⁿ⁻¹ (suc n) .fst))                     ≡⟨ ap (map ∘ map) (antipode≡flip (suc n)) ⟩
  map (map (flipΣⁿ (suc n)))                               ≡⟨ flipΣⁿ⁺² (suc n) ⟩
  flipΣⁿ (suc (suc (suc n)))                               ∎

hairy-ball : (n : Nat) → ((p : Sⁿ⁻¹ n) → Tⁿ⁻¹ n p) → flipΣⁿ n ≡ id
hairy-ball n sec = sym $ funext (λ p → cⁿ⁻¹ n p (sec p)) ∙ antipode≡flip n

-- Showing that this in turn implies that n-1 is odd requires more homotopy theory
-- than I have available: one can use πₙ(Sⁿ) ≃ ℤ to define the degree of a map,
-- which should be -1 for flipΣ and 1 for id.
