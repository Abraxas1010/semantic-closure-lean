/-!
# Closing the Loop: (F,A) diagram skeleton (Tier 2)

This module provides a *typed* graph/container to encode the shape of (F,A)-style
diagrams (as used in relational biology / semantic closure discussions) without
committing to a probabilistic or dynamical semantics.

The intent is to supply a stable target for later phases (e.g. temporal/DAG
factorizations) while keeping the present landing small and proof-friendly.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace FA

universe u

/-- A typed node, carrying a human-readable name and a Lean type. -/
structure Node where
  name : String
  ty : Type u

/-- A typed edge between two nodes. -/
structure Edge where
  src : Node.{u}
  dst : Node.{u}
  map : src.ty → dst.ty

/-- A finite typed diagram (nodes + edges). -/
structure Diagram where
  nodes : List Node
  edges : List Edge

end FA
end ClosingTheLoop
end HeytingLean

