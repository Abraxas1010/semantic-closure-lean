import HeytingLean.ClosingTheLoop.Semantics.KernelLaws
import HeytingLean.Process.Nucleus

/-!
# Closing the Loop: process semantics bridge (Tier 2)

This file connects `ClosingTheLoop`’s “semantic closure” language to the existing
process-calculus safety kernel `Process.Kproc`.

Key point:
`Kproc` is a **kernel** (contractive, meet-preserving, idempotent) on process predicates,
whose fixed points are exactly the safety properties closed under futures.

This is the concurrency-side analogue of preorder-time `futureKernel`.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Semantics

open Set

namespace ProcessBridge

open HeytingLean.Process

/-- `Process.Kproc` packaged as a generic `Semantics.Kernel`. -/
def KprocKernel : Kernel (α := ProcSet) where
  toFun := Kproc
  monotone' := Kproc_monotone
  map_inf' := by
    intro S T
    simpa [inf_eq_inter] using (Kproc_meet S T)
  idempotent' := by
    intro S
    simpa using (Kproc_idem S)
  apply_le' := by
    intro S
    exact Kproc_contract S

/-- “Well-typed in context `Γ`” is closed under futures, hence a fixed point of `Kproc`. -/
theorem wellTyped_fixedPoint (Γ : ChanCtx) :
    Kproc { P | WellTypedProc Γ P } = { P | WellTypedProc Γ P } :=
  Kproc_wellTyped_eq Γ

end ProcessBridge

end Semantics
end ClosingTheLoop
end HeytingLean

