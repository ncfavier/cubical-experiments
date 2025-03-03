{-# OPTIONS --cubical --erasure --rewriting #-}
open import Agda.Primitive renaming (Set to Type; Setω to Typeω)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Axiom.Extensionality.Propositional
open import Data.Product
import Cubical.Foundations.Prelude as 🧊
import Cubical.Foundations.CartesianKanOps as 🧊
{-# BUILTIN REWRITE _≡_ #-}

-- Investigating the erasure modality
module Erasure where

private variable
  a b : Level
  A : Type a

-- The erased path induction principle J₀

J₀-type =
  ∀ {a b} {@0 A : Type a} {@0 x : A} (B : (@0 y : A) → @0 x ≡ y → Type b)
  → {@0 y : A} (@0 p : x ≡ y) → B x refl → B y p

-- The Erased monadic modality

record Erased (@0 A : Type a) : Type a where
  constructor [_]
  field
    @0 erased : A

open Erased

η : {@0 A : Type a} → A → Erased A
η x = [ x ]

μ : {@0 A : Type a} → Erased (Erased A) → Erased A
μ [ [ x ] ] = [ x ]

-- Paths (Erased A) → Erased (Paths A)
erased-cong : ∀ {a} {@0 A : Type a} {@0 x y : A} → [ x ] ≡ [ y ] → Erased (x ≡ y)
erased-cong p = [ cong erased p ]

-- Erased (Paths A) → Paths (Erased A) ("erasure extensionality")
[]-cong-type = ∀ {a} {@0 A : Type a} {@0 x y : A} → Erased (x ≡ y) → [ x ] ≡ [ y ]

-- J₀ and []-cong (with their respective computation rules) are interderivable

module J₀→[]-cong where
  postulate
    J₀ : J₀-type
    J₀-refl
      : ∀ {a b} {@0 A : Type a} {@0 x : A} (B : (@0 y : A) → @0 x ≡ y → Type b) (r : B x refl)
      → J₀ B refl r ≡ r
    {-# REWRITE J₀-refl #-}

  []-cong : []-cong-type
  []-cong {x} [ p ] = J₀ (λ y _ → [ x ] ≡ [ y ]) p refl

  []-cong-refl
    : ∀ {a} {@0 A : Type a} {@0 x : A}
    → []-cong {x = x} [ refl ] ≡ refl
  []-cong-refl = refl

module []-cong→J₀ where
  postulate
    []-cong : []-cong-type
    []-cong-refl
      : ∀ {a} {@0 A : Type a} {@0 x : A}
      → []-cong {x = x} [ refl ] ≡ refl
    {-# REWRITE []-cong-refl #-}

  --                        []-cong                        μ
  -- Erased (Paths (Erased A)) → Paths (Erased (Erased A)) → Paths (Erased A)
  stable-≡ : ∀ {@0 A : Type a} {x y : Erased A} → Erased (x ≡ y) → x ≡ y
  stable-≡ p = cong μ ([]-cong p)

  --         η               []-cong          erased-cong
  -- Paths A → Erased (Paths A) → Paths (Erased A) → Erased (Paths A)
  --           Erased (Paths A)           →          Erased (Paths A)
  --                                      id
  []-cong-section'
    : ∀ {@0 A : Type a} {@0 x y : A} (p : x ≡ y)
    → erased-cong ([]-cong (η p)) ≡ η p
  []-cong-section' refl = refl

  -- We can cancel out η by unique elimination and stability of paths in Erased
  []-cong-section
    : ∀ {@0 A : Type a} {@0 x y : A} (@0 p : x ≡ y)
    → erased-cong ([]-cong [ p ]) ≡ [ p ]
  []-cong-section p = stable-≡ [ []-cong-section' p ]

  J₀ : J₀-type
  J₀ B {y} p r = subst (λ ([ p ]) → B y p) ([]-cong-section p) b'
    where
      b' : B y (cong erased ([]-cong [ p ]))
      b' = J (λ ([ y ]) p → B y (cong erased p)) ([]-cong [ p ]) r

  J₀-refl
    : ∀ {a b} {@0 A : Type a} {@0 x : A} (B : (@0 y : A) → @0 x ≡ y → Type b) (r : B x refl)
    → J₀ B refl r ≡ r
  J₀-refl B r = refl

-- Function extensionality implies erasure extensionality
module funext→[]-cong where
  postulate
    funext : ∀ {a b} → Extensionality a b

  -- Direct proof, extracted from "Logical properties of a modality for erasure" (Danielsson 2019)

  -- id : Paths (Erased A) → Paths (Erased A)
  --    → {funext}
  --      Paths (Paths (Erased A) → Erased A)
  --    → {uniquely eliminating}
  --      Paths (Erased (Paths (Erased A)) → Erased A)
  --    → {apply p}
  --      Paths (Erased A)
  stable-≡ : ∀ {@0 A : Type a} {x y : Erased A} → Erased (x ≡ y) → x ≡ y
  stable-≡ {A} {x} {y} [ p ] =
    cong (λ (f : x ≡ y → Erased A) → [ f p .erased ])
         (funext (λ (p : x ≡ y) → p))

  --                  η                        stable-≡
  -- Erased (Paths A) → Erased (Paths (Erased A)) → Paths (Erased A)
  []-cong : []-cong-type
  []-cong [ p ] = stable-≡ [ cong η p ]

  -- Alternative proof: ignoring some details, the types of funext and []-cong look very similar:
  --   funext  : Functions (Paths A) → Paths (Functions A)
  --   []-cong : Erased    (Paths A) → Paths (Erased    A)
  --
  -- If we have inductive types with erased constructors, then we can
  -- present erasure as an *open subtopos* generated by the subterminal
  -- object with a single erased point:

  data None : Type where
    @0 none : None

  ○'_ : Type a → Type a
  ○' A = None → A

  ○_ : ○' Type a → Type a
  ○ A = (n : None) → A n

  E→○ : {A : ○' Type a} → Erased (A none) → ○ A
  E→○ [ a ] none = a

  ○→E : {A : ○' Type a} → ○ A → Erased (A none)
  ○→E f = [ f none ]

  E→○→E : {A : ○' Type a} → (a : Erased (A none)) → ○→E (E→○ {A = A} a) ≡ a
  E→○→E _ = refl

  -- We don't actually need this
  ○→E→○ : {A : ○' Type a} → (f : ○ A) → E→○ (○→E f) ≡ f
  ○→E→○ f = funext (E→○ [ refl {x = f none} ])

  -- Since Erased is (equivalent to) a function type, erasure extensionality/[]-cong
  -- is a special case of function extensionality:
  --
  --                                   funext
  -- Erased (Paths A) ≃ (None → Paths A) → Paths (None → A) ≃ Paths (Erased A)
  []-cong' : []-cong-type
  []-cong' {A} {x} {y} p = cong ○→E x'≡y'
    where
      x' y' : ○ E→○ [ A ]
      x' = E→○ [ x ]
      y' = E→○ [ y ]

      x'≡y' : x' ≡ y'
      x'≡y' = funext (E→○ p)

  -- The reflector into the corresponding *closed* subtopos of ○-connected types
  -- is given by the join with None, which is equivalent to the following HIT
  -- (we enter cubical land here):
  data ●_ (A : Type a) : Type a where
    -- At runtime, we only have A.
    ●-η : A → ● A
    -- At compile time, we also have an erased "cone" that glues all of A together,
    -- so that ● A is contractible.
    @0 none : ● A
    @0 glue : (a : A) → ●-η a 🧊.≡ none

  @0 ●-○-connected : ∀ {A : Type a} → 🧊.isContr (● A)
  ●-○-connected {A} = none 🧊., cone where
    cone : (a : ● A) → none 🧊.≡ a
    cone (●-η a) = 🧊.sym (glue a)
    cone none = 🧊.refl
    cone (glue a i) j = glue a (i 🧊.∨ 🧊.~ j)

  -- Fracture and gluing

  ○'-η : {A : Type a} → A → ○' A
  ○'-η a _ = a

  ●-map : {A : Type a} {B : Type b} → (A → B) → ● A → ● B
  ●-map f (●-η a) = ●-η (f a)
  ●-map f none = none
  ●-map f (glue a i) = glue (f a) i

  ○→●○ : {A : Type a} → ○' A → ● ○' A
  ○→●○ = ●-η

  ●→●○ : {A : Type a} → ● A → ● ○' A
  ●→●○ = ●-map ○'-η

  module _ (A : Type a) where
    record Fracture : Type a where
      field
        op : ○' A
        cl : ● A
        agree : ○→●○ op 🧊.≡ ●→●○ cl

    open Fracture

    fracture : A → Fracture
    fracture a .op = ○'-η a
    fracture a .cl = ●-η a
    fracture a .agree = 🧊.refl

    gluing : Fracture → A
    gluing f = go (f .op) (f .cl) (f .agree)
      where
        go : (op : ○' A) → (cl : ● A) → ○→●○ op 🧊.≡ ●→●○ cl → A
        go op (●-η a) agree = a
        go op none agree = op none
        go op (glue a i) agree = {! 🧊.coei→0 (λ i → ●-η op 🧊.≡ glue (λ _ → a) i) i agree   !}

    gluing-fracture : ∀ a → gluing (fracture a) ≡ a
    gluing-fracture a = {!   !}

    fracture-gluing : ∀ f → fracture (gluing f) ≡ f
    fracture-gluing f = {!   !}
