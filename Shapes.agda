open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Relation.Nullary

-- —
data Interval : Type where
  l : Interval
  r : Interval
  seg : l ≡ r

Interval-isContr : isContr Interval
Interval-isContr = l , paths where
  paths : (x : Interval) → l ≡ x
  paths l = refl
  paths r = seg
  paths (seg i) j = seg (i ∧ j)

Interval-loops : (x : Interval) → x ≡ x
Interval-loops l = refl
Interval-loops r = refl
Interval-loops (seg i) j = seg i

-- ○
data S¹ : Type where
  base : S¹
  loop : base ≡ base

S¹→⊤ : S¹ → ⊤
S¹→⊤ base = tt
S¹→⊤ (loop i) = tt
⊤→S¹ : ⊤ → S¹
⊤→S¹ tt = base
⊤→S¹→⊤ : (t : ⊤) → S¹→⊤ (⊤→S¹ t) ≡ t
⊤→S¹→⊤ tt = refl
-- S¹→⊤→S¹ : (x : S¹) → ⊤→S¹ (S¹→⊤ x) ≡ x
-- S¹→⊤→S¹ base = refl
-- S¹→⊤→S¹ (loop i) j = {! IMPOSSIBLE the point doesn't retract onto the circle! !}

always-loop : (x : S¹) → x ≡ x
always-loop base = loop
always-loop (loop i) j =
  hcomp (λ where k (i = i0) → loop (j ∨ ~ k)
                 k (i = i1) → loop (j ∧ k)
                 k (j = i0) → loop (i ∨ ~ k)
                 k (j = i1) → loop (i ∧ k))
        base

-- ●
data D² : Type where
  base² : D²
  loop² : base² ≡ base²
  disk : refl ≡ loop²

D²-isContr : isContr D²
D²-isContr = base² , paths where
  paths : (x : D²) → base² ≡ x
  paths base² = refl
  paths (loop² i) j = disk j i
  paths (disk i j) k = disk (i ∧ k) j

D²-isProp : isProp D²
D²-isProp x y = sym (D²-isContr .snd x) ∙ D²-isContr .snd y
