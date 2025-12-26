# Categorical Foundations (Noneism Extension)

This document records the categorical vocabulary used by the Noneism layer and points to the corresponding Lean modules.

## Dictionary

| Noneism concept | Categorical structure | Lean module |
|---|---|---|
| Minimal zero | Initial object / empty type | `HeytingLean/Noneism/Zeros/Minimal.lean` |
| Maximal zero | Presheaf category `[Cᵒᵖ, Type]` | `HeytingLean/Noneism/Cat/Presheaf.lean`, `HeytingLean/Noneism/Zeros/Maximal.lean` |
| Potentialize | Yoneda embedding `C ⥤ [Cᵒᵖ, Type]` | `HeytingLean/Noneism/Cat/Yoneda.lean` |
| Actualize | Choose a representing object for a representable presheaf | `HeytingLean/Noneism/Cat/Yoneda.lean` |
| Recursive zero | Fixed-point locus of a nucleus (idempotent endomap/monad) | `HeytingLean/Noneism/Core/Nucleus.lean`, `HeytingLean/Noneism/Zeros/Recursive.lean` |
| Dynamics | Endofunctor / coalgebra | `HeytingLean/Noneism/Cat/Coalgebra.lean` |
| Eigenform | Fixed point / initial algebra (Lambek-style statement) | `HeytingLean/Noneism/Cat/FixedPoint.lean` |
| Self-reference | Lawvere fixed point theorem (type-level formulation) | `HeytingLean/Noneism/Cat/Lawvere.lean` |

## 0D as presheaves (maximal zero)

The presheaf category is used as a “space of probes”:

- File: `HeytingLean/Noneism/Cat/Presheaf.lean`
- Definition: `HeytingLean.Noneism.Cat.Presheaf`

This is the technical meaning of “all potentialities”: it contains generalized objects and their observable behavior under all tests.

## The crossing as Yoneda + representability

The Yoneda embedding packages each object by its functor of points.

- File: `HeytingLean/Noneism/Cat/Yoneda.lean`
- Names:
  - `HeytingLean.Noneism.Cat.potentialize`
  - `HeytingLean.Noneism.Cat.potentializeFullyFaithful`

The “actualization” step is modeled by representability: a presheaf that is isomorphic to `yoneda.obj X` is represented by an object `X`, and such an `X` is unique up to unique isomorphism.

Lean interface (mathlib):

- `Functor.IsRepresentable`
- `Functor.RepresentableBy`
- `Functor.RepresentableBy.uniqueUpToIso`

In the bundle:

- `HeytingLean.Noneism.Cat.actualize` chooses a representing object (classical choice).
- `HeytingLean.Noneism.Cat.actualizeIso` records uniqueness up to iso.

This is the categorical analogue of the “dynamics-grounded” interpretation: the object is not arbitrary once representability is fixed (it is forced up to a unique isomorphism).

## Nucleus as idempotent monad

The Closure work already uses an inflationary idempotent operator `R` on a lattice/frame. The Noneism layer records the same idea in a categorical vocabulary:

- File: `HeytingLean/Noneism/Cat/Monad.lean`
- File: `HeytingLean/Noneism/Core/Nucleus.lean`

The fixed-point locus `Ω_R := {x | R x = x}` is interpreted as the stable/eigen part.

## Dynamics as coalgebra and fixed points

Dynamics can also be expressed as coalgebraic structure for an endofunctor.

- File: `HeytingLean/Noneism/Cat/Coalgebra.lean`

The existence of fixed points is expressed abstractly (and related to the `Eigen` packaging).

- File: `HeytingLean/Noneism/Cat/FixedPoint.lean`

## Lawvere fixed point theorem (type-level form)

The bundle includes a minimal type-level fixed point theorem: a point-surjective `A → (A → B)` yields fixed points for all endomaps `B → B`.

- File: `HeytingLean/Noneism/Cat/Lawvere.lean`
- Theorem: `HeytingLean.Noneism.Cat.fixedPoint_of_surjective_eval`

This provides a precise, mechanized statement of the slogan “self-reference forces eigenforms”.

## Zero hierarchy package

For convenience, the three layers are bundled as a record:

- File: `HeytingLean/Noneism/Zeros/Hierarchy.lean`
- Definition: `HeytingLean.Noneism.Zeros.ZeroHierarchy`

This is intentionally lightweight: it is a wiring harness for documentation and future extensions (e.g. linking 0D/1D to the existing nucleus/semantic-closure pipeline).

