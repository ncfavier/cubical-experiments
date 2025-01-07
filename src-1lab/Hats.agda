open import 1Lab.Path.Reasoning
open import 1Lab.Prelude

open import Algebra.Monoid.Category
open import Algebra.Group

open import Data.List hiding (lookup)
open import Data.Fin
open import Data.Fin.Closure

open is-iso

{-
This is a formalisation of a hat puzzle whose statement you can read at any
of these places:

  https://www.jsoftware.com/pipermail/general/2007-June/030272.html
  https://www.cut-the-knot.org/blue/PuzzleWithHats.shtml
  https://twitter.com/gro_tsen/status/1618989823100096512

🎩 SPOILERS AHEAD! 🎩
-}
module Hats where

-- We assume there's at least one person, and that everyone has a unique
-- "name" between 0 and n - 1, known to everyone else.
module _ (n-1 : Nat) where
  private
    n = suc n-1
    Person = Fin n
    Hat = Fin n
    Hats = Person → Hat

  record Strategy : Type where
    -- `guess i xs` is the guess made by the ith person upon seeing the n - 1
    -- other hats given by `xs` (a vector of numbers from 0 to n - 1).
    field
      guess : Person → (Fin n-1 → Hat) → Hat

    -- The relation `hats ✓ i` means that the ith person guesses correctly,
    -- given the assignment `hats`.
    _✓_ : Hats → Person → Type
    hats ✓ i = guess i (delete hats i) ≡ hats i

    -- We are interested in strategies where at least one person guesses
    -- correctly for every assignment of hats.
    field
      one-right : ∀ hats → Σ Person λ i → hats ✓ i

    -- First, note that, given this requirement, there can be at *most* one
    -- correct guess for every assignment of hats.
    -- This follows from a probabilistic argument: every person guesses correctly
    -- with probability 1/n, so the total number of correct guesses across all
    -- hat assignments is nⁿ.
    -- In order to conclude, we use the fact that any surjection between finite
    -- sets of equal cardinality is an equivalence.
    exactly-one-right : ∀ hats → is-contr (Σ Person λ i → hats ✓ i)
    exactly-one-right hats = Equiv→is-hlevel 0 (Fibre-equiv _ hats e⁻¹) (p-is-equiv .is-eqv hats)
      where
        probability : ∀ i → Iso (Σ Hats (_✓ i)) (Fin n-1 → Hat)
        probability i .fst (hats , _) = delete hats i
        probability i .snd .inv other .fst = other [ i ≔ guess i other ]
        probability i .snd .inv other .snd =
          guess i ⌜ delete (other [ i ≔ guess i other ]) i ⌝ ≡⟨ ap! (funext (delete-insert _ i _)) ⟩
          guess i other                                      ≡˘⟨ insert-lookup _ i _ ⟩
          (other [ i ≔ guess i other ]) i                    ∎
        probability i .snd .rinv _ = funext (delete-insert _ i _)
        probability i .snd .linv (hats , r) = Σ-prop-path! (funext (insert-delete _ i _ (sym r)))

        only-one : Σ Hats (λ hats → Σ Person (hats ✓_)) ≃ Hats
        only-one =
          Σ _ (λ hats → Σ _ λ i → hats ✓ i) ≃⟨ Σ-swap₂ ⟩
          Σ _ (λ i → Σ _ λ hats → hats ✓ i) ≃⟨ Σ-ap-snd (Iso→Equiv ∘ probability) ⟩
          Fin n × (Fin n-1 → Fin n)         ≃˘⟨ Fin-suc-Π ⟩
          (Fin n → Fin n)                   ≃∎

        p : Σ Hats (λ hats → Σ Person (hats ✓_)) → Hats
        p = fst
        p-is-equiv : is-equiv p
        p-is-equiv = Finite-surjection→equiv (inc only-one) p
          λ other → inc ((other , one-right other) , refl)

  open Strategy public

  -- n-hypercubes of order m. We won't use the extra degree of generality,
  -- but it doesn't hurt.
  Hypercube : Nat → Type
  Hypercube m = (Fin n → Fin m) → Fin m

  -- Latin hypercubes, or n-ary quasigroups.
  -- Every number appears exactly once on each "line"; equivalently,
  -- every partial application to n - 1 coordinates is an automorphism.
  is-latin : ∀ {m} → Hypercube m → Type
  is-latin {m} h = ∀ (i : Fin n) (xs : Fin n-1 → Fin m) → is-equiv λ x → h (xs [ i ≔ x ])

  Latin-hypercube : Nat → Type
  Latin-hypercube m = Σ (Hypercube m) is-latin

  -- Every latin n-hypercube h of order n induces a strategy where everyone
  -- guesses that the multiplication of all the hats is equal to their index.
  latin→strategy : Latin-hypercube n → Strategy
  latin→strategy (h , lat) .guess i other = equiv→inverse (lat i other) i
  latin→strategy (h , lat) .one-right hats =
    h hats , Equiv.from (eqv (h hats)) refl
    where
      module L i = Equiv (_ , lat i (delete hats i))
      eqv : ∀ (i : Fin n) → (L.from i i ≡ hats i) ≃ (h hats ≡ i)
      eqv i =
        L.from i i ≡ hats i ≃⟨ Equiv.adjunct (L.inverse i) ⟩
        i ≡ L.to i (hats i) ≃⟨ sym-equiv ⟩
        L.to i (hats i) ≡ i ≃⟨ ∙-pre-equiv (sym (ap h (funext (insert-delete hats i _ refl)))) ⟩
        h hats ≡ i          ≃∎

  -- In particular, every group structure on Fin n induces a strategy since
  -- group multiplication is an n-ary equivalence.
  group→latin : Group-on (Fin n) → Latin-hypercube n
  group→latin G = mul , mul-equiv
    where
      open Group-on G hiding (magma-hlevel)

      mul : ∀ {m} → (Fin m → Fin n) → Fin n
      mul xs = fold underlying-monoid (tabulate xs)

      mul-equiv : ∀ {m} (i : Fin (suc m)) (xs : Fin m → Fin n)
                → is-equiv (λ x → mul (xs [ i ≔ x ]))
      mul-equiv i xs with fin-view i
      mul-equiv _ xs | zero = ⋆-equivr _
      mul-equiv {suc m} _ xs | suc i = ∙-is-equiv (mul-equiv i (xs ∘ fsuc)) (⋆-equivl _)

  group→strategy : Group-on (Fin n) → Strategy
  group→strategy = latin→strategy ∘ group→latin
