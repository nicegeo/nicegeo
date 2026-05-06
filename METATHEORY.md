This is a working documentation file on the difference between our implementation of System E and the core theory presented in the System E paper (and the reference embedded formalizations we used), as well as any open metatheoretical questions we have.

# Primitives

## Core Logic

Our base logic is our kernel's dependent type theory, which is loosely the Calculus of Constructions with a universe hierarchy (no inductive types). Basic logical primitives for E along with their introduction and elimination rules are axiomatized at the synthetic layer, as are propositional equality and lists (there is an underlying definitional equality in our kernel). The E paper's base logic is some kind of FOL (I think, need to ask more about this) with quantifiers, above which a sequent calculus is applied. 

## Sorts

The E paper has points, lines, circles, segments, angles, and areas as separate sorts. Our core type theory, in contrast, has two language-level sorts (`Prop` and `Type`, though with universes we have many levels of `Type`). Then, `Point`, `Line`, and `Circle` are embedded/synthetic sorts, in the sense of having type `Type`, but are not represented as sorts to the kernel. In the meantime, segments, angles, and areas all use one single `Measure` embedded/synthetic sort (also something of type `Type`). This more closely matches one of the Lean embeddings of E.

## Basic Relations

The axiomatizations of the basic relations over the first three sorts from the paper (on, same-side, between, inside, center, and intersects) are all the same in our synthetic layer. 

## Magnitudes/Measures

As mentioned above, the last three sorts (magnitudes in the paper) are all one `Measure` in our synthetic layer. We have axiomatizations of less than, the constant zero, and the addition function. The basic properties of these are axiomatized as well. 

## Construction Rules

The construction rules match one-to-one (though the comments do not), with the addition of a `distinct_from` predicate that is axiomatized (this appears to be optional in the paper) which has its own introduction and elimination rule separate from the point introduction and elimination rules (which in turn use our axiomatization of `List.mem`). The sixth point construction rule diverges (see #165); unsure which version (ours or the paper's) is correct, but I will document that here once I know more. In the ninth point construction rule, "outside" is interpreted as "neither in or on," which is how it is described earlier in the E paper as an abbreviation. We do not explicitly define `outside`, though.

# Diagrammatic Inferences

## Generalities

These match completely with the paper.

## Between Axioms

These are also aligned completely with the paper, though there is a mistake the _comment_ for the first one (see the first comment in #164).

## Same Side Axioms

These are also aligned completely with the paper.

## Pasch Axioms

These are also aligned completely with the paper.

## Triple Incidence

These are aligned completely with the paper.

## Circle Axioms

These appear completely aligned with the paper. Distinctness is interpreted as inequality, which works due to other axioms (see discussion from #168).

## Intersection Rules

Most of the axioms are the same, but the fourth axiom is changed to fix a mistake in the original paper.
The paper reads:

> If a is on or inside α, b is on or inside α, a is inside β, and b is outside β, then α and β intersect.

But, as noted in #143, this is unsound, as can be seen by letting β be an arbitrarily small circle around a. We replaced that axiom with what we believe the intended behavior to be:

> If a is on α, b is on or inside α, a is inside β, and b is outside β, then α and β intersect.

But we are unsure of the completeness implications of this change.

In the meantime, we have a bug in the first two of our intersection rules, described in #169, that we need to fix.

## Equality Axioms

These are the same, this is just moved upward in the file when we first axiomatize equality, and denoted explicitly as introduction and elimination rules in the standard type-theoretic fashion. 

# Metric Inferences

The measure axioms are the same as in the paper (though we have a single sort, as noted earlier), they just appear early in the file when we first axiomatize `Measure`. The remaining axioms are formalized in a way that is straightforwardly faithful to the paper.

# Transfer Inferences

## Diagram-Segment Transfer Axioms

These are straightforwardly faithful to the paper.

## Diagram-Angle Transfer Axioms

These are straightforwardly faithful to the paper.

## Diagram-Area Transfer Axioms

These are straightforwardly faithful to the paper.

# Superposition

We directly axiomatize SSS and SAS rather than a single superposition axiom from which we can project to prove SAS and SSS. 

# Direct Consequence

We just axiomatize the classical proof by contradiction axiom without worrying too much about the discussion in the paper of intuitinoistic proof and complexity and so on. Notably, the paper says that the specific double-negation-elimination principle does not, in their sequent calculus model, imply LEM. But in our base logic, the version of DNE we added definitely does imply LEM! We have plans in #144 to add a way to tag/track tactics and proofs that use the classical axiom, and we think this is a satisfactory compromise. 
