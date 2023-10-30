open import 1Lab.Type
open import 1Lab.Type.Sigma
open import 1Lab.Type.Pointed
open import 1Lab.Path
open import 1Lab.HLevel
open import 1Lab.HLevel.Retracts
open import 1Lab.Equiv

module ObjectClassifier where

-- The type of arrows/bundles/fibrations.
Bundle : ∀ ℓ → Type (lsuc ℓ)
Bundle ℓ
  = Σ (Type ℓ) λ A
  → Σ (Type ℓ) λ B
  → A → B

-- The standard pullback construction (HoTT book 2.15.11).
record Pullback {ℓ ℓ'} {B : Type ℓ} {C D : Type ℓ'} (s : B → D) (q : C → D) : Type (ℓ ⊔ ℓ') where
  constructor pb
  field
    pb₁ : B
    pb₂ : C
    pbeq : s pb₁ ≡ q pb₂

open Pullback

pb-path : ∀ {ℓ ℓ'} {B : Type ℓ} {C D : Type ℓ'} {s : B → D} {q : C → D} → {a b : Pullback s q}
        → (p1 : a .pb₁ ≡ b .pb₁) → (p2 : a .pb₂ ≡ b .pb₂) → PathP (λ i → s (p1 i) ≡ q (p2 i)) (a .pbeq) (b .pbeq)
        → a ≡ b
pb-path p1 p2 pe i = pb (p1 i) (p2 i) (pe i)

-- The morphisms of interest between bundles p : A → B and q : C → D are pairs
-- r : A → C, s : B → D that make a *pullback square*:
--                r
--           A ------> C
--           | ⯾       |
--         p |         | q
--           v         v
--           B ------> D
--                s
-- Rather than laboriously state the universal property of a pullback, we take it
-- on faith that the construction above has the universal property (this is
-- exercise 2.11 in the HoTT book) and simply define "being a pullback" as having
-- r and p factor through an equivalence A ≃ Pullback s q.
-- This completely determines r by the factorisation r = pb₂ ∘ e .fst, so we can
-- omit it by contractibility of singletons.
_⇒_ : ∀ {ℓ} {ℓ'} → Bundle ℓ → Bundle ℓ' → Type (ℓ ⊔ ℓ')
(A , B , p) ⇒ (C , D , q)
  = Σ (B → D) λ s
  → Σ (A ≃ Pullback s q) λ e
  → p ≡ pb₁ ∘ e .fst

-- An object classifier is a *universal* bundle U∙ → U such that any other
-- bundle has a unique map (i.e. pullback square) into it.
-- Categorically, it is a terminal object in the category of arrows and pullback squares.
is-classifier : ∀ {ℓ} → Bundle (lsuc ℓ) → Type (lsuc ℓ)
is-classifier {ℓ} u = ∀ (p : Bundle ℓ) → is-contr (p ⇒ u)

-- The projection from the type of pointed types to the type of types is our
-- universal bundle: the fibre above A : Type ℓ is equivalent to A itself.
Type↓ : ∀ ℓ → Bundle (lsuc ℓ)
Type↓ ℓ = Type∙ ℓ , Type ℓ , fst

Type↓-fibre : ∀ {ℓ} (A : Type ℓ) → A ≃ Pullback {B = Lift ℓ ⊤} {C = Type∙ ℓ} (λ _ → A) fst
Type↓-fibre A = Iso→Equiv λ where
  .fst a → pb _ (A , a) refl
  .snd .is-iso.inv (pb _ (A' , a) eq) → transport (sym eq) a
  .snd .is-iso.linv → transport-refl
  .snd .is-iso.rinv (pb _ (A' , a) eq) → pb-path refl (sym (Σ-path (sym eq) refl)) λ i j → eq (i ∧ j)

postulate
  -- We assume that Type↓ is an object classifier in the sense above, and show that
  -- this makes it a univalent universe.
  Type↓-is-classifier : ∀ {ℓ} → is-classifier (Type↓ ℓ)

-- Every type is trivially a bundle over the unit type.
! : ∀ {ℓ} → Type ℓ → Bundle ℓ
! A = A , Lift _ ⊤ , _

-- The key observation is that the type of pullback squares from ! A to Type↓ is
-- equivalent to the type of types equipped with an equivalence to A.
-- Since the former was assumed to be contractible, so is the latter.
lemma : ∀ {ℓ} (A : Type ℓ) → (! A ⇒ Type↓ ℓ) ≃ Σ (Type ℓ) (λ B → A ≃ B)
lemma {ℓ} A = Iso→Equiv λ where
  .fst (ty , e , _) → ty _ , e ∙e Type↓-fibre (ty _) e⁻¹
  .snd .is-iso.inv (B , e) → (λ _ → B) , e ∙e Type↓-fibre B , refl
  .snd .is-iso.linv (ty , e , _) → Σ-pathp refl (Σ-pathp (Σ-prop-path is-equiv-is-prop
    (funext λ _ → Equiv.ε (Type↓-fibre (ty _)) _)) refl)
  .snd .is-iso.rinv (B , e) → Σ-pathp refl (Σ-prop-path is-equiv-is-prop
    (funext λ _ → Equiv.η (Type↓-fibre B) _))

-- Equivalences form an identity system, which is another way to state univalence.
univalence : ∀ {ℓ} (A : Type ℓ) → is-contr (Σ (Type ℓ) λ B → A ≃ B)
univalence {ℓ} A = is-hlevel≃ 0 (lemma A e⁻¹) (Type↓-is-classifier (! _))
