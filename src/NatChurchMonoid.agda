open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.Instances.Nat
open import Cubical.Algebra.Semigroup
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

-- ℕ ≃ (m : Monoid) → ⟨ m ⟩ → ⟨ m ⟩
module NatChurchMonoid where

MEndo : Type₁
MEndo = (m : Monoid ℓ-zero) → ⟨ m ⟩ → ⟨ m ⟩

isNatural : MEndo → Type₁
isNatural me = {m1 m2 : Monoid ℓ-zero} (f : MonoidHom m1 m2) → me m2 ∘ f .fst ≡ f .fst ∘ me m1

isPropIsNatural : (me : MEndo) → isProp (isNatural me)
isPropIsNatural me a b i {m1} {m2} f j x = m2 .snd .MonoidStr.isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set (me m2 (f .fst x)) (f .fst (me m1 x)) (funExt⁻ (a f) x) (funExt⁻ (b f) x) i j

MEndoNatural : Type₁
MEndoNatural = Σ MEndo isNatural

-- A generalised Church encoding for ℕ. This boils down to the fact that the forgetful functor
-- U : Mon → Set is represented by ℕ ≃ F 1, followed by the Yoneda lemma.
ℕ≃MEndoNatural : Iso ℕ MEndoNatural
ℕ≃MEndoNatural = iso mtimes on1 mtimes-on1 on1-mtimes where

  mtimes : ℕ → MEndoNatural
  mtimes zero .fst (_ , monoidstr ε _·_ m) = (λ _ → ε)
  mtimes zero .snd f = funExt λ _ → sym (f .snd .IsMonoidHom.presε)
  mtimes (suc n) .fst ms@(t , monoidstr ε _·_ m) = (λ x → x · mtimes n .fst ms x)
  mtimes (suc n) .snd {m1} {m2@(_ , monoidstr _ _·_ m)} f = funExt λ x → cong (f .fst x ·_) (λ i → mtimes n .snd f i x) ∙ sym (f .snd .IsMonoidHom.pres· x (mtimes n .fst m1 x))

  mtimes-hom : (m : Monoid ℓ-zero) (x : ⟨ m ⟩) → MonoidHom NatMonoid m
  mtimes-hom m x = (λ n → mtimes n .fst m x) , monoidequiv refl (λ n n' → mtimes-+ n n') where
    mtimes-+ : (n n' : ℕ) {m : Monoid ℓ-zero} {x : ⟨ m ⟩} → mtimes (n + n') .fst m x ≡ m .snd .MonoidStr._·_ (mtimes n .fst m x) (mtimes n' .fst m x)
    mtimes-+ zero n' {m} = sym (m .snd .MonoidStr.isMonoid .IsMonoid.·IdL _)
    mtimes-+ (suc n) n' {m} {x} = cong (m .snd .MonoidStr._·_ x) (mtimes-+ n n') ∙ m .snd .MonoidStr.isMonoid .IsMonoid.isSemigroup .IsSemigroup.·Assoc _ _ _

  on1 : MEndoNatural → ℕ
  on1 me = me .fst NatMonoid 1

  on1-mtimes : (n : ℕ) → on1 (mtimes n) ≡ n
  on1-mtimes zero = refl
  on1-mtimes (suc n) = cong suc (on1-mtimes n)

  mtimes-on1 : (me : MEndoNatural) → mtimes (on1 me) ≡ me
  mtimes-on1 me = Σ≡Prop isPropIsNatural (λ i m x → p m x i) where
    p : (m : Monoid ℓ-zero) (x : ⟨ m ⟩) → mtimes (on1 me) .fst m x ≡ me .fst m x
    p m x = sym (funExt⁻ (me .snd (mtimes-hom m x)) 1)
          ∙ cong (me .fst m) (m .snd .MonoidStr.isMonoid .IsMonoid.·IdR _)
