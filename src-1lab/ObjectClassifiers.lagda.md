```agda
module ObjectClassifiers where
```

<details>
<summary>
Imports and basic definitions.
</summary>

```agda
open import 1Lab.Type hiding (⊤)
open import 1Lab.Type.Pointed
open import 1Lab.Type.Sigma
open import 1Lab.Path
open import 1Lab.Equiv
open import 1Lab.HLevel
open import 1Lab.HLevel.Closure
open import 1Lab.Extensionality
open import Data.Id.Base

open import 1Lab.Univalence
  using (Fibre-equiv) -- this does not use univalence

-- The (homotopy) pullback, defined using the inductive identity type to
-- make some things easier
record
  Pullback
    {ℓ ℓ' ℓ''} {B : Type ℓ} {C : Type ℓ'} {D : Type ℓ''}
    (s : B → D) (q : C → D)
  : Type (ℓ ⊔ ℓ' ⊔ ℓ'') where
  constructor pb
  field
    pb₁ : B
    pb₂ : C
    pbeq : s pb₁ ≡ᵢ q pb₂

open Pullback

-- A universe-polymorphic unit type to avoid Lift noise
record ⊤ {u} : Type u where
  constructor tt
```
</details>

It is well-known that univalent universes in type theory correspond to
object classifiers in higher topos theory. However, there are a few different ways
to make sense of this internally to type theory itself.

In what follows, we fix a (Russell) universe $\mathcal{U}$ and call types
in $\mathcal{U}$ *small*. We write
$\mathcal{U}^\mathsf{p} : \mathcal{U}^\bullet \to \mathcal{U}$ for the
universal projection from pointed small types to small
types. We assume function extensionality (implicitly by working in Cubical Agda),
but *not* univalence.

```agda
module _ {u} where

  U  = Type u
  U∙ = Type∙ u
  U⁺ = Type (lsuc u)

  Uᵖ : U∙ → U
  Uᵖ (A , _) = A
```

We *define* univalence for $\mathcal{U}$ as the statement that the type
$(Y : \mathcal{U}) \times X \simeq Y$ is contractible for all $X : \mathcal{U}$
(thus that equivalences form an identity system on $\mathcal{U}$).
We will also refer to $n$-univalence, the restriction of that statement
to the sub-universe of $n$-types in $\mathcal{U}$.

```agda
  univalence = {X : U} → is-contr (Σ U λ Y → X ≃ Y)
```

Given a "base" type $B : \mathcal{U}$, there are two main ways we can express
"type families over $B$" in type theory: as maps *into* $B$ from a small
domain (this is often called the "fibred" perspective, and such maps may be
called "fibrations" or "bundles" over $B$), or as maps *out* of $B$ into
the universe (the "indexed" perspective). We thus define:

$$
\begin{align*}
\mathsf{Bun}(B) &= (A : \mathcal{U}) \times \begin{matrix}A \\ \downarrow \\ B\end{matrix}\\
\mathsf{Fam}(B) &= B \to \mathcal{U}
\end{align*}
$$

```agda
  module _ (B : U) where

    Bun : U⁺
    Bun = Σ[ A ∈ U ] (A → B)

    Fam : U⁺
    Fam = B → U
```

We have maps between those in both directions: the map $\chi_B : \mathsf{Bun}(B) \to
\mathsf{Fam}(B)$ assigns to a bundle $A \to B$ its family of *fibres*, while
the map $\phi_B : \mathsf{Fam}(B) \to \mathsf{Bun}(B)$ assigns to a $B$-indexed
family the first projection out of its *total space*.

```agda
    χ : Bun → Fam
    χ (A , p) = fibre p

    φ : Fam → Bun
    φ a = Σ B a , fst
```

The [HoTT book](https://homotopytypetheory.org/book/) proves (theorem 4.8.3) that
$\chi_B$ and $\phi_B$ are inverses, assuming that $\mathcal{U}$ is univalent. This is also
formalised in the 1Lab:

```agda
    _ : is-equiv χ
    _ = 1Lab.Univalence.Fibration-equiv {ℓ' = u} .snd

    _ : is-equiv φ
    _ = (1Lab.Univalence.Fibration-equiv {ℓ' = u} e⁻¹) .snd
```

A partial converse to this result was formalised independently by
Martín Escardó (in [TypeTopology](https://martinescardo.github.io/TypeTopology/UF.Classifiers.html)) and by Amélia Liao (in [this math.SE answer](https://math.stackexchange.com/a/4364416)): both of them show that univalence follows from $\chi_B$ being a fibrewise equivalence
**if one also assumes $(-2)$-univalence**, i.e. that any two contractible
types are equal^[This is implied by propositional extensionality, i.e. $(-1)$-univalence.] (as well as function extensionality).
In [this Mastodon post](https://types.pl/@ncf/114737741485982172) I gave
an example of a Tarski universe containing two distinct unit types and which
can be closed under $\Sigma$- and identity types in such a way that $\chi_B$ and
$\phi_B$ are both fibrewise equivalences, but which is not $n$-univalent for any $n$, thus
suggesting that one cannot get rid of the $(-2)$-univalence assumption.

In this note I would like to suggest an explanation for *why* the converse of theorem 4.8.3 fails.
The key is to notice that $\mathsf{Bun}(B)$ and $\mathsf{Fam}(B)$ can be thought of as
the endpoints of a *span* of types whose apex is the type of *pullback squares* with
bottom-left corner $B$ and right-hand side map $\mathcal{U}^\mathsf{p}$:

~~~{.quiver}
% https://q.uiver.app/#q=WzAsNCxbMCwxLCJCIl0sWzEsMSwiXFxtYXRoY2Fse1V9Il0sWzEsMCwiXFxtYXRoY2Fse1V9XlxcYnVsbGV0Il0sWzAsMCwiQSIsWzI3MCw2MCw2MCwxXV0sWzAsMSwiYSIsMix7ImNvbG91ciI6WzI3MCw2MCw2MF19LFsyNzAsNjAsNjAsMV1dLFsyLDEsIlxcbWF0aGNhbHtVfV5cXG1hdGhzZntwfSJdLFszLDAsInAiLDIseyJjb2xvdXIiOlsyNzAsNjAsNjBdfSxbMjcwLDYwLDYwLDFdXSxbMywyLCJhXisiLDAseyJjb2xvdXIiOlsyNzAsNjAsNjBdfSxbMjcwLDYwLDYwLDFdXSxbMywxLCIiLDEseyJjb2xvdXIiOlsyNzAsNjAsNjBdLCJzdHlsZSI6eyJuYW1lIjoiY29ybmVyIn19XV0=
\[\begin{tikzcd}
	\textcolor{accent2}{A} & {\mathcal{U}^\bullet} \\
	B & {\mathcal{U}}
	\arrow["{a^+}", color={accent2}, from=1-1, to=1-2]
	\arrow["p"', color={accent2}, from=1-1, to=2-1]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, color={accent2}, draw=none, from=1-1, to=2-2]
	\arrow["{\mathcal{U}^\mathsf{p}}", from=1-2, to=2-2]
	\arrow["a"', color={accent2}, from=2-1, to=2-2]
\end{tikzcd}\]
~~~

Let us call such a pullback square a *classification* over $B$: it consists of
a fibration over $B$ that is classified by a given map $a : B \to \mathcal{U}$.

To define the type $\mathsf{Cls}(B)$ of classifications, we take a shortcut: instead of recording three maps and a
universal property, we only record the top-left corner $A$ and the bottom map $a$,
and ask for an equivalence between $A$ and a given pullback of $\mathcal{U}^\mathsf{p}$
along $a$. This fully determines the projection maps out of $A$,
so we are justified in leaving them out by function extensionality and contractibility of singletons.
Note that we *cannot* similarly contract $A$ away as that would implicitly assume univalence.

```agda
    record Cls : U⁺ where
      constructor cls
      field
        A : U
        a : B → U
        classifies : A ≃ Pullback a Uᵖ

      module c = Equiv classifies

      p : A → B
      p = pb₁ ∘ c.to

      a⁺ : A → U∙
      a⁺ = pb₂ ∘ c.to
```

We obtain the span promised above by projecting the left and bottom maps of the
pullback square, respectively.

~~~{.quiver}
% https://q.uiver.app/#q=WzAsMyxbMCwwLCJcXG1hdGhzZntCdW59KEIpIl0sWzEsMCwiXFxtYXRoc2Z7Q2xzfShCKSJdLFsyLDAsIlxcbWF0aHNme0ZhbX0oQikiXSxbMSwwLCJcXHBpX1xcZG93bmFycm93IiwyXSxbMSwyLCJcXHBpX1xccmlnaHRhcnJvdyJdXQ==
\[\begin{tikzcd}
	{\mathsf{Bun}(B)} & {\mathsf{Cls}(B)} & {\mathsf{Fam}(B)}
	\arrow["{\pi_\downarrow}"', from=1-2, to=1-1]
	\arrow["{\pi_\rightarrow}", from=1-2, to=1-3]
\end{tikzcd}\]
~~~

```agda
    π↓ : Cls → Bun
    π↓ p = _ , Cls.p p

    π→ : Cls → Fam
    π→ = Cls.a
```

Observe that both $\pi_\downarrow$ and $\pi_\to$ have sections, given by
taking fibres and total spaces respectively, and that composing one
section with the other projection recovers the maps $\chi_B$ and $\phi_B$.

~~~{.quiver}
% https://q.uiver.app/#q=WzAsMyxbMCwwLCJcXG1hdGhzZntCdW59KEIpIl0sWzEsMCwiXFxtYXRoc2Z7Q2xzfShCKSJdLFsyLDAsIlxcbWF0aHNme0ZhbX0oQikiXSxbMSwwLCJcXHBpX1xcZG93bmFycm93IiwwLHsib2Zmc2V0IjotMn1dLFsxLDIsIlxccGlfXFxyaWdodGFycm93IiwwLHsib2Zmc2V0IjotMn1dLFswLDEsIlxcc2lnbWFfXFxkb3duYXJyb3ciLDAseyJvZmZzZXQiOi0yfV0sWzIsMSwiXFxzaWdtYV9cXHRvIiwwLHsib2Zmc2V0IjotMn1dLFswLDIsIlxcY2hpX0IiLDAseyJjdXJ2ZSI6LTN9XSxbMiwwLCJcXHBoaV9CIiwwLHsiY3VydmUiOi0zfV1d
\[\begin{tikzcd}
	{\mathsf{Bun}(B)} & {\mathsf{Cls}(B)} & {\mathsf{Fam}(B)}
	\arrow["{\sigma_\downarrow}", shift left=2, from=1-1, to=1-2]
	\arrow["{\chi_B}", curve={height=-35pt}, from=1-1, to=1-3]
	\arrow["{\pi_\downarrow}", shift left=2, from=1-2, to=1-1]
	\arrow["{\pi_\rightarrow}", shift left=2, from=1-2, to=1-3]
	\arrow["{\phi_B}", curve={height=-35pt}, from=1-3, to=1-1]
	\arrow["{\sigma_\to}", shift left=2, from=1-3, to=1-2]
\end{tikzcd}\]
~~~

```agda
    σ↓ : Bun → Cls
    σ↓ (A , p) = λ where
      .Cls.A → A
      .Cls.a → fibre p
      .Cls.classifies .fst a → pb (p a) (fibre p (p a) , a , refl) reflᵢ
      .Cls.classifies .snd → is-iso→is-equiv λ where
        .is-iso.from (pb b (_ , (a , _)) reflᵢ) → a
        .is-iso.rinv (pb b (_ , (a , eq)) reflᵢ) i →
          pb (eq i) (fibre p (eq i) , a , λ j → eq (i ∧ j)) reflᵢ
        .is-iso.linv _ → refl

    section↓ : is-right-inverse σ↓ π↓
    section↓ (A , p) = refl

    _ : π→ ∘ σ↓ ≡ χ
    _ = refl

    σ→ : Fam → Cls
    σ→ a = λ where
      .Cls.A → Σ B a
      .Cls.a → a
      .Cls.classifies .fst (b , x) → pb b (a b , x) reflᵢ
      .Cls.classifies .snd → is-iso→is-equiv λ where
        .is-iso.from (pb b (_ , x) reflᵢ) → b , x
        .is-iso.rinv (pb b (_ , x) reflᵢ) → refl
        .is-iso.linv _ → refl

    section→ : is-right-inverse σ→ π→
    section→ a = refl

    _ : π↓ ∘ σ→ ≡ φ
    _ = refl
```

We now come to the main point of this post: **each of $\pi_\downarrow$ and $\pi_\to$
is an equivalence if and only if univalence holds**.
This is reflected in the proof of [`Fibration-equiv`{.Agda}](https://1lab.dev/1Lab.Univalence#Fibration-equiv), which uses
univalence *twice*, once in the left inverse proof and once in the right inverse proof.
This suggests that the two uses of univalence *cancel each other out* in a certain
sense, so that we lose information if we only ask for a composite equivalence
between $\mathsf{Bun}(B)$ and $\mathsf{Fam}(B)$.

In more detail, the statement that $\pi_\downarrow$ is an equivalence says that
every bundle $A \to B$ is classified by a unique^[That is, a contractible space of.] pullback square into
$\mathcal{U}^\mathsf{p}$; this looks a lot like the definition of an
[object classifier](https://ncatlab.org/nlab/show/%28sub%29object+classifier+in+an+%28infinity%2C1%29-topos) in higher topos theory!
On the other hand, the statement that $\pi_\to$ is an equivalence says that
every map $B \to \mathcal{U}$ has a unique pullback along $\mathcal{U}^\mathsf{p}$;
in other words, that this pullback is determined uniquely up to *identity*
rather than just equivalence.
Notice that both statements are roughly of the form "there is a unique pullback square",
but that they quantify over different *parts* of the pullback square.

The easiest way to substantiate our claim is to specialise $B$ to the unit type;
in this case, the span simplifies to the two projections out of the type of
equivalences in $\mathcal{U}$:

~~~{.quiver}
% https://q.uiver.app/#q=WzAsNixbMCwwLCJcXG1hdGhzZntCdW59KFxcdG9wKSJdLFsxLDAsIlxcbWF0aHNme0Nsc30oXFx0b3ApIl0sWzIsMCwiXFxtYXRoc2Z7RmFtfShcXHRvcCkiXSxbMCwxLCJcXG1hdGhjYWx7VX0iXSxbMSwxLCIoWCwgWSA6IFxcbWF0aGNhbHtVfSkgXFx0aW1lcyBYIFxcc2ltZXEgWSJdLFsyLDEsIlxcbWF0aGNhbHtVfSJdLFsxLDAsIlxccGlfXFxkb3duYXJyb3ciLDJdLFsxLDIsIlxccGlfXFx0byJdLFswLDMsIlxcc2ltIiwyXSxbMSw0LCJcXHNpbSIsMl0sWzIsNSwiXFxzaW0iLDJdLFs0LDUsIlxccGleXFxzaW1lcV8yIiwyXSxbNCwzLCJcXHBpXlxcc2ltZXFfMSJdXQ==
\[\begin{tikzcd}
	{\mathsf{Bun}(\top)} & {\mathsf{Cls}(\top)} & {\mathsf{Fam}(\top)} \\
	{\mathcal{U}} & {(X, Y : \mathcal{U}) \times X \simeq Y} & {\mathcal{U}}
	\arrow["\sim"', from=1-1, to=2-1]
	\arrow["{\pi_\downarrow}"', from=1-2, to=1-1]
	\arrow["{\pi_\to}", from=1-2, to=1-3]
	\arrow["\sim"', from=1-2, to=2-2]
	\arrow["\sim"', from=1-3, to=2-3]
	\arrow["{\pi^\simeq_1}", from=2-2, to=2-1]
	\arrow["{\pi^\simeq_2}"', from=2-2, to=2-3]
\end{tikzcd}\]
~~~

```agda
  Equiv : U⁺
  Equiv = Σ[ X ∈ U ] Σ[ Y ∈ U ] X ≃ Y

  π₁≃ : Equiv → U
  π₁≃ (X , Y , e) = X

  π₂≃ : Equiv → U
  π₂≃ (X , Y , e) = Y

  Fam⊤≃U : Fam ⊤ ≃ U
  Fam⊤≃U .fst a = a _
  Fam⊤≃U .snd = is-iso→is-equiv λ where
    .is-iso.from X _ → X
    .is-iso.rinv X → refl
    .is-iso.linv a → refl

  Bun⊤≃U : Bun ⊤ ≃ U
  Bun⊤≃U .fst (A , _) = A
  Bun⊤≃U .snd = is-iso→is-equiv λ where
    .is-iso.from X → X , _
    .is-iso.rinv _ → refl
    .is-iso.linv _ → refl

  Pullback≃a : {a : ⊤ {u} → U} → Pullback a Uᵖ ≃ a _
  Pullback≃a .fst (pb _ (_ , b) reflᵢ) = b
  Pullback≃a .snd = is-iso→is-equiv λ where
    .is-iso.from b → pb _ (_ , b) reflᵢ
    .is-iso.rinv _ → refl
    .is-iso.linv (pb _ (_ , b) reflᵢ) → refl

  Cls⊤≃Equiv : Cls ⊤ ≃ Equiv
  Cls⊤≃Equiv .fst (cls A a e) = A , a _ , e ∙e Pullback≃a
  Cls⊤≃Equiv .snd = is-iso→is-equiv λ where
    .is-iso.from (X , Y , e) → cls X (λ _ → Y) (e ∙e Pullback≃a e⁻¹)
    .is-iso.rinv (X , Y , e) → refl ,ₚ refl ,ₚ ext λ _ → refl
    .is-iso.linv (cls A a e) →
      let
        h : (e ∙e Pullback≃a) ∙e Pullback≃a e⁻¹ ≡ e
        h = ext λ _ → Equiv.η Pullback≃a _
      in λ i → cls A a (h i)

  _ : π₁≃ ≡ Equiv.to Bun⊤≃U ∘ π↓ ⊤ ∘ Equiv.from Cls⊤≃Equiv
  _ = refl

  _ : π₂≃ ≡ Equiv.to Fam⊤≃U ∘ π→ ⊤ ∘ Equiv.from Cls⊤≃Equiv
  _ = refl
```

This makes the proof immediate after noting that the fibre of $\pi^\simeq_1$ at
$X$ is equivalent to $(Y : \mathcal{U}) \times X \simeq Y$ (a general fact
that does not require univalence or even function extensionality), and
symmetrically for $\pi^\simeq_2$.

```agda
  π₁≃-equiv→univalence : is-equiv π₁≃ → univalence
  π₁≃-equiv→univalence h {X} = Equiv→is-hlevel 0
    (Fibre-equiv (λ X → Σ U λ Y → X ≃ Y) X e⁻¹)
    (h .is-eqv X)

  π↓-equiv→univalence : is-left-inverse (σ↓ ⊤) (π↓ ⊤) → univalence
  π↓-equiv→univalence h = π₁≃-equiv→univalence $
    ∘-is-equiv (Bun⊤≃U .snd)
      (∘-is-equiv π↓-is-equiv
        ((Cls⊤≃Equiv e⁻¹) .snd))
    where
      π↓-is-equiv : is-equiv (π↓ ⊤)
      π↓-is-equiv = is-iso→is-equiv (iso (σ↓ _) (section↓ _) h)

  sym≃ : Equiv ≃ Equiv
  sym≃ .fst (X , Y , e) = Y , X , e e⁻¹
  sym≃ .snd = is-involutive→is-equiv λ (X , Y , e) →
    refl ,ₚ refl ,ₚ ext λ _ → refl

  π→-equiv→univalence : is-left-inverse (σ→ ⊤) (π→ ⊤) → univalence
  π→-equiv→univalence h = π₁≃-equiv→univalence $
    ∘-is-equiv (Fam⊤≃U .snd)
      (∘-is-equiv π→-is-equiv
        (∘-is-equiv ((Cls⊤≃Equiv e⁻¹) .snd)
          (sym≃ .snd)))
    where
      π→-is-equiv : is-equiv (π→ ⊤)
      π→-is-equiv = is-iso→is-equiv (iso (σ→ _) (section→ _) h)
```

It also makes it easy to see the complete loss of information in assuming
an equivalence $\mathsf{Bun}(\top) \simeq \mathsf{Fam}(\top)$, since this
amounts to the trivial $\mathcal{U} \simeq \mathcal{U}$! Assuming that
$\chi_\top$ or $\phi_\top$ is an equivalence doesn't get us very far either,
as in both cases we just get that forming products with a contractible type is an
equivalence.

```agda
  _ : Equiv.to Bun⊤≃U ∘ π↓ ⊤ ∘ σ→ ⊤ ∘ Equiv.from Fam⊤≃U
    ≡ λ X → ⊤ × X
  _ = refl

  _ : Equiv.to Fam⊤≃U ∘ π→ ⊤ ∘ σ↓ ⊤ ∘ Equiv.from Bun⊤≃U
    ≡ λ X → X × tt ≡ tt
  _ = refl
```
