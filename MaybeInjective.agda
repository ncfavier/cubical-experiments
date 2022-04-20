module MaybeInjective where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything renaming (Iso to _≅_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Equality hiding (_≡c_; reflc)
open import Cubical.Data.Maybe

fun : {A B : Type} → Maybe A ≃ Maybe B → A → B
fun ma≃mb a with equivFun ma≃mb (just a) in eqj
fun ma≃mb a | just b = b
fun ma≃mb a | nothing with equivFun ma≃mb nothing in eqn
fun ma≃mb a | nothing | just b = b
fun ma≃mb a | nothing | nothing = ⊥.rec (¬just≡nothing j≡n) where
  j≡n : just a ≡ nothing
  j≡n = invEq (congEquiv ma≃mb) (ptoc eqj ∙ sym (ptoc eqn))

maybeInjective : {A B : Type} → Maybe A ≡ Maybe B → A ≡ B
maybeInjective {A} {B} ma≡mb = ua (a→b , equiv) where
  ma≃mb = pathToEquiv ma≡mb
  mb≃ma = invEquiv ma≃mb
  a→b = fun ma≃mb
  b→a = fun mb≃ma
  b→a→b : (b : B) → a→b (b→a b) ≡ b
  b→a→b b = _ -- screw this
  equiv : isEquiv a→b
  equiv .equiv-proof b = (b→a b , b→a→b b) , _ -- and this
