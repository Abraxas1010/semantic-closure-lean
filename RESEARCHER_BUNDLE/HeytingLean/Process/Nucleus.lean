import Mathlib.Data.Set.Lattice
import HeytingLean.Process.Syntax
import HeytingLean.Process.Semantics
import HeytingLean.Process.Typing

/-!
Process kernel `K S = {P | ∀ P', P ⟶* P' → P' ∈ S}` capturing safety invariants closed under futures.
-/
namespace HeytingLean
namespace Process

open Classical Set

abbrev ProcSet := Set Proc

def Kproc (S : ProcSet) : ProcSet :=
  { P | ∀ P', (P ⟶* P') → P' ∈ S }

/-- The kernel is contractive: every future-closed process lies in the original set. -/
lemma Kproc_contract (S : ProcSet) : Kproc S ⊆ S := by
  intro P hP; simpa using hP P (ReducesStar.refl P)

/-- `Kproc` is monotone in its argument set. -/
lemma Kproc_monotone : Monotone Kproc := by
  intro S T hST P h; exact fun P' hPP' => hST (h P' hPP')

/-- Applying `Kproc` twice yields the same kernel (idempotence). -/
lemma Kproc_idem (S : ProcSet) : Kproc (Kproc S) = Kproc S := by
  funext P; apply propext; constructor
  · intro h Q hPQ
    have hQKS : Q ∈ Kproc S := h Q hPQ
    -- evaluate membership at Q itself
    exact hQKS Q (ReducesStar.refl Q)
  · intro h Q hPQ R hQR
    exact h R (ReducesStar.trans hPQ hQR)

/-- The kernel preserves intersections of process sets. -/
lemma Kproc_meet (S T : ProcSet) : Kproc (S ∩ T) = Kproc S ∩ Kproc T := by
  funext P; apply propext; constructor
  · intro h; refine And.intro (fun Q hPQ => (h Q hPQ).1) (fun Q hPQ => (h Q hPQ).2)
  · intro h Q hPQ; exact And.intro (h.1 Q hPQ) (h.2 Q hPQ)

/- A lightweight lens wrapper (kernel-style) -/
structure ProcessKernel where
  R : ProcSet → ProcSet
  mono : Monotone R
  idem : ∀ S, R (R S) = R S
  meet_preserve : ∀ S T, R (S ∩ T) = R S ∩ R T

@[simp] def kernel : ProcessKernel where
  R := Kproc
  mono := Kproc_monotone
  idem := Kproc_idem
  meet_preserve := Kproc_meet

/-- If a process set is closed under the multi-step reduction relation, then it
is a fixed point of the kernel operator `Kproc`. -/
lemma Kproc_eq_of_closed (S : ProcSet)
    (hClosed : ∀ P P', P ⟶* P' → P ∈ S → P' ∈ S) :
    Kproc S = S := by
  funext P; apply propext; constructor
  · intro hP; exact Kproc_contract S hP
  · intro hP Q hPQ
    exact hClosed P Q hPQ hP

/-- The set of well-typed processes for a fixed context is closed under the
multi-step reduction relation (`ReducesStar`). -/
lemma typed_closed (Γ : ChanCtx) :
    ∀ P P', P ⟶* P' → WellTypedProc Γ P → WellTypedProc Γ P' := by
  intro P P' hPP' hP
  exact ReducesStar.subject_reduction hP hPP'

/-- For the safety predicate “well-typed in context Γ”, the process kernel
`Kproc` is exact: it returns exactly the well-typed processes. -/
lemma Kproc_wellTyped_eq (Γ : ChanCtx) :
    Kproc { P | WellTypedProc Γ P } = { P | WellTypedProc Γ P } := by
  apply Kproc_eq_of_closed
  intro P P' hPP' hP
  exact typed_closed Γ P P' hPP' hP

end Process
end HeytingLean
