# The Eigencomputable Framework (Noneism Extension)

This document explains the new Noneism layer added to the researcher bundle and how it refines the interpretation of nonconstructive definitions in the semantic-closure mechanization.

## The Problem: Binary computability is too coarse

Lean distinguishes:

- **Computable**: definable by `def` with executable content.
- **Noncomputable**: definable only using classical principles (typically `Classical.choice`).

In the Closure development, the closure map `β` (inverse evaluation) is constructed from surjectivity by classical choice. This is mathematically valid, but it conflates two distinct situations:

1. *Arbitrary choice*: existence without any stabilizing mechanism.
2. *Dynamics-grounded choice*: existence where the value is forced by a uniqueness/attractor property.

The Noneism thesis formalizes (2) as an intermediate notion.

## The Three-Level Hierarchy (Operational)

| Level | Lean marker | Meaning |
|------:|------------:|---------|
| Computable | `def` | Algorithm exists and runs. |
| Eigencomputable | `@[eigencomputable D]` + `noncomputable` | Not algorithmic, but uniquely determined by dynamics `D`. |
| Arbitrary noncomputable | `noncomputable def` (no tag) | Uses classical selection without a grounding dynamics. |

The point is not to “ban” classical choice. It is to make explicit when a choice is justified by a stabilizing principle.

## Core definitions (Lean)

The heart of the framework is the `Eigen` type:

- File: `HeytingLean/Noneism/Eigen/Basic.lean`
- Names:
  - `HeytingLean.Noneism.IsEigenform`
  - `HeytingLean.Noneism.Eigen`
  - `HeytingLean.Noneism.Eigen.ofExistsUniqueFixedPoint`

Informally, `Eigen α` packages:

1. a dynamics `d : α → α`,
2. a value `a : α`,
3. a proof that `a` is the unique fixed point of `d`.

## Application: β as an eigencomputable construction

### Paper objects

For types `A B` and a chosen point `b : B`:

- `Metabolism` is `A → B`
- `Selector` is `B → (A → B)`
- `evalAt b` is evaluation-at-`b` on selectors: `Φ ↦ Φ b`

Lean definitions:

- File: `HeytingLean/Noneism/Bridge/EvaluationMap.lean`
- Names:
  - `HeytingLean.Noneism.Bridge.Metabolism`
  - `HeytingLean.Noneism.Bridge.Selector`
  - `HeytingLean.Noneism.Bridge.evalAt`

### The grounding dynamics

The dynamics on selectors “forgets everything but the value at `b`”:

- File: `HeytingLean/Noneism/Bridge/SelectorDynamics.lean`
- Names:
  - `HeytingLean.Noneism.Bridge.selectorDynamics`
  - `HeytingLean.Noneism.Bridge.selectorDynamicsAt`

Crucially, for each metabolism `f`, the fiber

`{Φ // evalAt b Φ = f}`

has a canonical dynamics `selectorDynamicsAt f` with a unique fixed point.

### β and its properties

`β` is defined by extracting that unique fixed point:

- File: `HeytingLean/Noneism/Bridge/BetaEigen.lean`
- Names:
  - `HeytingLean.Noneism.Bridge.betaEigenAt`
  - `HeytingLean.Noneism.Bridge.beta`
  - `HeytingLean.Noneism.Bridge.beta_right_inverse`
  - `HeytingLean.Noneism.Bridge.beta_stable`

The attribute `@[eigencomputable selectorDynamicsAt]` on `betaEigenAt` makes the “why” machine-checkable: this nonconstructive value is fixed by an explicit dynamics.

### Comparison with raw choice

- File: `HeytingLean/Noneism/Bridge/BetaConstruction.lean`
- Names:
  - `HeytingLean.Noneism.Bridge.betaRaw`
  - `HeytingLean.Noneism.Bridge.beta_eq_const`
  - `HeytingLean.Noneism.Bridge.beta_eq_betaRaw_of_stable`

`betaRaw` is the standard right-inverse built by classical choice from surjectivity. The comparison lemma shows: if a chosen right-inverse is stable under the selector dynamics, then it agrees with `beta`.

## Relation to the Closure mechanization

The Noneism layer does not replace the Closure development; it provides an additional interpretation layer and bridges.

- Bridge to the Closure MR structures:
  - File: `HeytingLean/Noneism/Bridge/SemanticClosureLink.lean`
  - File: `HeytingLean/Noneism/Bridge/MRClosure.lean`

## How to verify locally

From `RESEARCHER_BUNDLE/`:

1. Run the main Closure verifier: `./scripts/verify_closing_the_loop.sh`
2. Run the Noneism verifier: `./scripts/verify_noneism.sh`

The Noneism verifier builds the module and enumerates all declarations tagged with `@[eigencomputable ...]`.

