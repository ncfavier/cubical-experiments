open import 1Lab.Path.Reasoning
open import 1Lab.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Concrete
open import Algebra.Group.Ab

open import Cat.Prelude

open import Homotopy.Space.Delooping

-- This now lives at https://1lab.dev/Algebra.Group.Concrete.Abelian.html#first-abelian-group-cohomology
module FirstGroupCohomology where

open Precategory

π₁BG≡G : ∀ {ℓ} (G : Group ℓ) → π₁B (Concrete G) ≡ G
π₁BG≡G G = π₁B≡π₀₊₁ (Concrete G) ∙ sym (G≡π₁B G)

-- Any two loops commute in the delooping of an abelian group.
ab→square : ∀ {ℓ} {H : Group ℓ} (H-ab : is-commutative-group H)
          → {x : Deloop H} (p q : x ≡ x) → Square p q q p
ab→square {H = H} H-ab {x} = Deloop-elim-prop H (λ x → (p q : x ≡ x) → Square p q q p) (λ _ → hlevel 1)
  (λ p q → commutes→square (subst is-commutative-group (sym (π₁BG≡G H)) H-ab p q)) x

module _ {ℓ} (G : Group ℓ) (H : Group ℓ) (H-ab : is-commutative-group H) where
  -- The first cohomology of G with coefficients in H.
  -- We will show that it is equivalent to the set of group homomorphisms from G
  -- to H, assuming that H is abelian.
  H¹[G,H] = ∥ (Deloop G → Deloop H) ∥₀

  unpoint : (Deloop∙ G →∙ Deloop∙ H) → H¹[G,H]
  unpoint (f , _) = inc f

  work : ∀ f → f base ≡ base → is-contr (fibre unpoint (inc f))
  work f ptf .centre = (f , ptf) , refl
  work f ptf .paths ((g , ptg) , g≡f) = Σ-prop-path! (Σ-pathp
    (funext (Deloop-elim-set G _ (λ _ → hlevel 2) (ptf ∙ sym ptg) λ z → rec!
      (λ g≡f → J
        (λ g _ → ∀ ptg → Square (ap f (path z)) (ptf ∙ sym ptg) (ptf ∙ sym ptg) (ap g (path z)))
        (λ _ → ab→square H-ab _ _)
        (sym g≡f) ptg)
      (∥-∥₀-path.to g≡f)))
    (flip₂ (∙-filler'' ptf (sym ptg))))

  unpoint-is-equiv : is-equiv unpoint
  unpoint-is-equiv .is-eqv = ∥-∥₀-elim (λ _ → hlevel 2)
    λ f → rec! (work f) (Deloop-is-connected (f base))

  unpoint≃ : H¹[G,H] ≃ (Deloop∙ G →∙ Deloop∙ H)
  unpoint≃ = (unpoint , unpoint-is-equiv) e⁻¹

  delooping : (Deloop∙ G →∙ Deloop∙ H) ≃ Hom (Groups ℓ) (π₁B (Concrete G)) (π₁B (Concrete H))
  delooping = _ , π₁F-is-ff {_} {Concrete G} {Concrete H}

  first-group-cohomology : H¹[G,H] ≃ Hom (Groups ℓ) G H
  first-group-cohomology = unpoint≃ ∙e delooping
    ∙e path→equiv (ap₂ (Hom (Groups ℓ)) (π₁BG≡G G) (π₁BG≡G H))

-- As a cool application, the space of endomorphisms of the delooping of ℤ/2ℤ has
-- exactly two connected components!
-- (But note that there is no type with exactly two endomorphisms: it would be a set,
-- and nⁿ = 2 has no integer solutions.)
