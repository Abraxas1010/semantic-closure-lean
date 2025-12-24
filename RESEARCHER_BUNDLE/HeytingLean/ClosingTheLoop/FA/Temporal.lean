import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# Closing the Loop: functorial temporal parametrization (F,A) (Tier 2)

This module upgrades the (F,A) “diagram skeleton” from static types to **time-indexed**
types using a general *time category* `T`.

Rationale (research agenda item 6):
- Different models of computation (λ-calculus vs process algebra) often share a categorical
  semantics in which *time evolution* is functorial.
- Using a general category `T` keeps the design neutral:
  - `T := ℕ` (as a category) recovers discrete time,
  - a preorder recovers causal partial orders / concurrency,
  - a tree-like category can encode branching futures (anticipation).

This file is intentionally a container layer only:
- It does **not** impose probabilistic semantics (e.g. joint distributions).
- It does **not** impose continuity or coalgebraic finality assumptions.

Those are later “semantics” phases.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace FA

open CategoryTheory

universe u v w

/-- A time-indexed node: a functor assigning a type/value space at each time object. -/
structure TemporalNode (T : Type u) [Category.{v} T] where
  name : String
  ty : T ⥤ Type w

/-- A time-indexed edge: a natural transformation between temporal nodes. -/
structure TemporalEdge (T : Type u) [Category.{v} T] where
  src : TemporalNode T
  dst : TemporalNode T
  map : src.ty ⟶ dst.ty

/-- A (finite) time-indexed diagram: temporal nodes + temporal edges. -/
structure TemporalDiagram (T : Type u) [Category.{v} T] where
  nodes : List (TemporalNode T)
  edges : List (TemporalEdge T)

end FA
end ClosingTheLoop
end HeytingLean
