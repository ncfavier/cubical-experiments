open import 1Lab.Prelude
open import Data.Dec
open import Data.Nat

{-
A formalisation of https://en.wikipedia.org/wiki/Wolf,_goat_and_cabbage_problem
to demonstrate proof by reflection.
-}
module Goat where

holds : ∀ {ℓ} (A : Type ℓ) ⦃ _ : Dec A ⦄ → Type
holds _ ⦃ yes _ ⦄ = ⊤
holds _ ⦃ no _ ⦄ = ⊥

data Side : Type where
  left right : Side

left≠right : ¬ left ≡ right
left≠right p = subst (λ { left → ⊤; right → ⊥ }) p tt

instance
  Discrete-Side : Discrete Side
  Discrete-Side {left} {left} = yes refl
  Discrete-Side {left} {right} = no left≠right
  Discrete-Side {right} {left} = no (left≠right ∘ sym)
  Discrete-Side {right} {right} = yes refl

cross : Side → Side
cross left = right
cross right = left

record State : Type where
  constructor state
  field
    farmer wolf goat cabbage : Side

open State

count-left : Side → Nat
count-left left = 1
count-left right = 0
count-lefts : State → Nat
count-lefts (state f w g c) = count-left f + count-left w + count-left g + count-left c

is-valid : State → Type
is-valid s@(state f w g c) = count-lefts s ≡ 2 → f ≡ g

record Valid-state : Type where
  constructor valid
  field
    has-state : State
    ⦃ has-valid ⦄ : holds (is-valid has-state)

open Valid-state

data Move : State → State → Type where
  go-alone : ∀ {s} → Move s (record s { farmer = cross (s .farmer) })
  take-wolf : ∀ {s} → Move s (record s { farmer = cross (s .farmer); wolf = cross (s .wolf) })
  take-goat : ∀ {s} → Move s (record s { farmer = cross (s .farmer); goat = cross (s .goat) })
  take-cabbage : ∀ {s} → Move s (record s { farmer = cross (s .farmer); cabbage = cross (s .cabbage) })

data Moves : Valid-state → Valid-state → Type where
  done : ∀ {s} → Moves s s
  _∷_ : ∀ {a b c} ⦃ _ : holds (is-valid b) ⦄ → Move (a .has-state) b → Moves (valid b) c → Moves a c

infixr 6 _∷_

initial final : Valid-state
initial = valid (state left left left left)
final = valid (state right right right right)

goal : Moves initial final
goal = take-goat ∷ go-alone ∷ take-wolf ∷ take-goat ∷ take-cabbage ∷ go-alone ∷ take-goat ∷ done
-- goal = {! take-wolf ∷ ? !} -- No instance of type holds (is-valid ...) was found in scope.
